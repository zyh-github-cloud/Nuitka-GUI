import os
import sys
import re
import json
import threading
import queue
import subprocess
import tempfile
import time
import modulefinder
import platform
import shutil
import logging
from subprocess import TimeoutExpired
from PIL import Image
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QTabWidget, QGroupBox,
                             QLabel, QLineEdit, QPushButton, QRadioButton, QCheckBox, QListWidget, QProgressBar,
                             QTextEdit, QMessageBox, QFileDialog, QInputDialog, QButtonGroup, QSlider,
                             QDialog, QFrame, QComboBox, QProgressDialog, QGridLayout)
from PySide6.QtGui import QTextCursor, QIcon, QColor, QLinearGradient, QFont, QPainter, QPen
from PySide6.QtCore import Qt, QTimer, QPoint, QThread, Signal, QMutex, QMutexLocker

# 导入帮助内容模块
from help_content import get_help_content

# 缓存相关导入
import hashlib
import pickle
from datetime import datetime, timedelta

# 配置日志系统
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

# 常量定义
CACHE_EXPIRY_DAYS = 7  # 缓存过期时间（天）
MAX_WORKERS = min(4, os.cpu_count() or 4)  # 最大工作线程数
DEFAULT_TIMEOUT = 30  # 默认命令超时时间（秒）

class NeumorphicButton(QPushButton):
    """现代简洁风格按钮
    
    这是一个自定义按钮类，实现了现代简洁的设计风格，
    具有统一的渐变背景、圆角边框和优雅的悬停效果。
    支持DPI自适应显示，提供一致的用户体验。
    """
    def __init__(self, text, parent=None):
        super().__init__(text, parent)
        # 获取父窗口的DPI缩放比例，如果没有则使用默认值
        if parent and hasattr(parent, 'dpi_scale'):
            self.dpi_scale = parent.dpi_scale
        else:
            # 如果没有父窗口或父窗口没有dpi_scale属性，使用默认缩放
            screen = QApplication.primaryScreen()
            self.dpi_scale = screen.logicalDotsPerInch() / 96.0
        
        self.setFixedHeight(self.get_scaled_size(36))  # 统一按钮高度
        self.setCursor(Qt.PointingHandCursor)  # 设置鼠标指针为手型
        
        # 设置按钮字体为微软雅黑加粗
        font = self.font()
        font.setFamily("Microsoft YaHei")
        font.setPointSize(int(12 * self.dpi_scale))  # 统一字体大小
        font.setBold(True)
        self.setFont(font)
        
        # 应用统一样式
        self.setStyleSheet("""
            NeumorphicButton {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #B3E5FC, stop: 1 #81D4FA);
                color: #01579B;
                border: none;
                border-radius: 18px;
                padding: 8px 16px;
                font-weight: bold;
                font-size: 14px;
                min-width: 80px;
                outline: none;
            }
            NeumorphicButton:hover {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #E1F5FE, stop: 1 #B3E5FC);
                margin-top: -1px;
                margin-bottom: 1px;
            }
            NeumorphicButton:pressed {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #81D4FA, stop: 1 #4FC3F7);
                margin-top: 1px;
                margin-bottom: -1px;
            }
            NeumorphicButton:disabled {
                background-color: #B0BEC5;
                color: #F5F5F5;
            }
        """)
    
    def get_scaled_size(self, base_size):
        """获取根据DPI缩放后的尺寸
        
        根据系统的DPI设置对尺寸进行缩放，确保在不同分辨率下
        显示效果一致。
        
        Args:
            base_size: 基础尺寸值
            
        Returns:
            int: 缩放后的尺寸值
        """
        return int(base_size * self.dpi_scale)

class CacheManager:
    """缓存管理器 - 管理Python和Nuitka版本检测结果的缓存
    
    优化特点：
    - 线程安全的缓存操作
    - 统一的错误处理和日志记录
    - 可配置的缓存过期时间
    - 缓存统计和自动清理功能
    - 统一的缓存文件格式
    """
    
    def __init__(self, cache_dir=None, expiry_days=CACHE_EXPIRY_DAYS):
        self.cache_dir = cache_dir or os.path.join(os.path.expanduser("~"), ".nuitka_packager_cache")
        self.version_cache_file = os.path.join(self.cache_dir, "version_cache.json")
        self.python_paths_cache_file = os.path.join(self.cache_dir, "python_paths_cache.pkl")
        self.cache_duration_days = expiry_days  # 缓存有效期
        self._mutex = QMutex()  # 线程锁，确保缓存操作线程安全
        self.stats = {
            'cache_hits': 0,
            'cache_misses': 0,
            'cache_writes': 0,
            'cache_errors': 0
        }
        
        # 确保缓存目录存在
        try:
            os.makedirs(self.cache_dir, exist_ok=True)
            logging.info(f"缓存目录已创建: {self.cache_dir}")
        except Exception as e:
            logging.error(f"创建缓存目录失败: {e}")
    
    def _get_cache_key(self, python_cmd):
        """根据Python命令生成缓存键
        
        Args:
            python_cmd (str): Python命令或路径
            
        Returns:
            str: 生成的MD5哈希键
        """
        try:
            # 获取绝对路径以确保一致性
            python_path = os.path.abspath(python_cmd) if os.path.exists(python_cmd) else str(python_cmd)
            return hashlib.md5(python_path.encode()).hexdigest()
        except Exception as e:
            logging.warning(f"生成缓存键失败: {e}，使用备用方法")
            return hashlib.md5(str(python_cmd).encode()).hexdigest()
    
    def get_cached_versions(self, python_cmd):
        """从缓存获取Python和Nuitka版本信息（线程安全）
        
        Args:
            python_cmd (str): Python可执行文件路径
            
        Returns:
            tuple: (python_version, nuitka_version) 如果缓存有效，否则返回(None, None)
        """
        with QMutexLocker(self._mutex):
            try:
                if not os.path.exists(self.version_cache_file):
                    self.stats['cache_misses'] += 1
                    return None, None
                
                with open(self.version_cache_file, 'r', encoding='utf-8') as f:
                    cache_data = json.load(f)
                
                cache_key = self._get_cache_key(python_cmd)
                
                if cache_key not in cache_data:
                    self.stats['cache_misses'] += 1
                    return None, None
                
                cached_entry = cache_data[cache_key]
                
                # 检查缓存是否过期
                try:
                    cache_time = datetime.fromisoformat(cached_entry.get('timestamp', ''))
                    if datetime.now() - cache_time > timedelta(days=self.cache_duration_days):
                        # 缓存已过期
                        del cache_data[cache_key]  # 删除过期条目
                        # 写回更新后的缓存
                        with open(self.version_cache_file, 'w', encoding='utf-8') as f:
                            json.dump(cache_data, f, indent=2, ensure_ascii=False)
                        self.stats['cache_misses'] += 1
                        return None, None
                except Exception as e:
                    logging.warning(f"解析缓存时间失败: {e}，视为过期")
                    self.stats['cache_misses'] += 1
                    return None, None
                
                # 缓存命中
                self.stats['cache_hits'] += 1
                python_version = cached_entry.get('python_version')
                nuitka_version = cached_entry.get('nuitka_version')
                
                logging.debug(f"缓存命中: {python_cmd} - Python: {python_version}, Nuitka: {nuitka_version}")
                return python_version, nuitka_version
                
            except json.JSONDecodeError as e:
                logging.error(f"解析缓存文件失败 (JSON错误): {e}")
                self.stats['cache_errors'] += 1
                return None, None
            except Exception as e:
                logging.error(f"读取缓存失败: {e}")
                self.stats['cache_errors'] += 1
                return None, None
    
    def save_cached_versions(self, python_cmd, python_version, nuitka_version):
        """保存版本信息到缓存（线程安全）
        
        Args:
            python_cmd (str): Python可执行文件路径
            python_version (str): Python版本信息
            nuitka_version (str): Nuitka版本信息
        """
        with QMutexLocker(self._mutex):
            try:
                cache_data = {}
                
                # 如果缓存文件已存在，先读取现有数据
                if os.path.exists(self.version_cache_file):
                    try:
                        with open(self.version_cache_file, 'r', encoding='utf-8') as f:
                            cache_data = json.load(f)
                    except Exception as e:
                        logging.warning(f"读取现有缓存失败: {e}，创建新缓存")
                        cache_data = {}
                
                cache_key = self._get_cache_key(python_cmd)
                
                # 保存新的缓存条目
                cache_data[cache_key] = {
                    'python_version': python_version,
                    'nuitka_version': nuitka_version,
                    'timestamp': datetime.now().isoformat(),
                    'python_cmd': python_cmd
                }
                
                # 确保目录仍然存在
                os.makedirs(self.cache_dir, exist_ok=True)
                
                with open(self.version_cache_file, 'w', encoding='utf-8') as f:
                    json.dump(cache_data, f, indent=2, ensure_ascii=False)
                
                self.stats['cache_writes'] += 1
                logging.debug(f"缓存已更新: {python_cmd}")
                
            except Exception as e:
                logging.error(f"保存缓存失败: {e}")
                self.stats['cache_errors'] += 1
    
    def clear_cache(self):
        """清除所有缓存（线程安全）
        
        Returns:
            bool: 清除成功返回True，失败返回False
        """
        with QMutexLocker(self._mutex):
            try:
                # 清除版本缓存
                if os.path.exists(self.version_cache_file):
                    os.remove(self.version_cache_file)
                    logging.info(f"版本缓存已清除: {self.version_cache_file}")
                
                # 清除Python路径缓存
                if os.path.exists(self.python_paths_cache_file):
                    os.remove(self.python_paths_cache_file)
                    logging.info(f"Python路径缓存已清除: {self.python_paths_cache_file}")
                
                # 重置统计信息
                self.stats = {
                    'cache_hits': 0,
                    'cache_misses': 0,
                    'cache_writes': 0,
                    'cache_errors': 0
                }
                
                return True
            except Exception as e:
                logging.error(f"清除缓存失败: {e}")
                self.stats['cache_errors'] += 1
                return False
    
    def get_cache_info(self):
        """获取缓存信息和统计数据
        
        Returns:
            str: 缓存信息摘要
        """
        with QMutexLocker(self._mutex):
            try:
                if not os.path.exists(self.version_cache_file):
                    return f"无缓存文件 | 命中: {self.stats['cache_hits']}, 未命中: {self.stats['cache_misses']}"
                
                with open(self.version_cache_file, 'r', encoding='utf-8') as f:
                    cache_data = json.load(f)
                
                cache_count = len(cache_data)
                
                # 获取最新的缓存时间
                latest_time = None
                for entry in cache_data.values():
                    try:
                        cache_time = datetime.fromisoformat(entry.get('timestamp', ''))
                        if latest_time is None or cache_time > latest_time:
                            latest_time = cache_time
                    except Exception:
                        continue
                
                latest_time_str = latest_time.strftime('%Y-%m-%d %H:%M:%S') if latest_time else "未知"
                
                return (
                    f"缓存条目数: {cache_count}, 最新缓存: {latest_time_str} | "
                    f"命中: {self.stats['cache_hits']}, 未命中: {self.stats['cache_misses']}, "
                    f"写入: {self.stats['cache_writes']}, 错误: {self.stats['cache_errors']}"
                )
                
            except Exception as e:
                logging.error(f"获取缓存信息失败: {e}")
                return f"获取缓存信息失败: {str(e)} | 命中: {self.stats['cache_hits']}, 未命中: {self.stats['cache_misses']}"
    
    def get_cached_python_paths(self, check_expiry=True):
        """从缓存获取Python路径列表（线程安全）
        
        Args:
            check_expiry (bool): 是否检查过期
            
        Returns:
            list: 缓存的Python路径列表，如果缓存无效则返回None
        """
        with QMutexLocker(self._mutex):
            try:
                if not os.path.exists(self.python_paths_cache_file):
                    self.stats['cache_misses'] += 1
                    return None
                
                # 检查是否过期
                if check_expiry:
                    cache_age = datetime.now() - datetime.fromtimestamp(os.path.getmtime(self.python_paths_cache_file))
                    if cache_age > timedelta(days=self.cache_duration_days):
                        logging.info(f"Python路径缓存已过期 ({cache_age} > {self.cache_duration_days}天)")
                        self.stats['cache_misses'] += 1
                        return None
                
                with open(self.python_paths_cache_file, 'rb') as f:
                    python_paths = pickle.load(f)
                
                # 验证数据完整性
                if isinstance(python_paths, list) and all(isinstance(path, str) for path in python_paths):
                    self.stats['cache_hits'] += 1
                    logging.debug(f"Python路径缓存命中，共{len(python_paths)}个路径")
                    return python_paths
                else:
                    logging.warning(f"Python路径缓存数据格式无效")
                    self.stats['cache_misses'] += 1
                    return None
                    
            except Exception as e:
                logging.error(f"读取Python路径缓存失败: {e}")
                self.stats['cache_errors'] += 1
                return None
    
    def save_cached_python_paths(self, python_paths):
        """保存Python路径列表到缓存（线程安全）
        
        Args:
            python_paths (list): Python路径列表
        """
        with QMutexLocker(self._mutex):
            try:
                # 验证输入数据
                if not isinstance(python_paths, list):
                    raise TypeError("python_paths必须是列表类型")
                
                # 确保目录仍然存在
                os.makedirs(self.cache_dir, exist_ok=True)
                
                with open(self.python_paths_cache_file, 'wb') as f:
                    pickle.dump(python_paths, f, protocol=pickle.HIGHEST_PROTOCOL)
                
                self.stats['cache_writes'] += 1
                logging.info(f"Python路径缓存已保存，共{len(python_paths)}个路径")
                
            except Exception as e:
                logging.error(f"保存Python路径缓存失败: {e}")
                self.stats['cache_errors'] += 1
    
    def cleanup_expired_cache(self):
        """清理过期缓存项
        
        Returns:
            int: 清理的过期条目数量
        """
        with QMutexLocker(self._mutex):
            try:
                if not os.path.exists(self.version_cache_file):
                    return 0
                
                with open(self.version_cache_file, 'r', encoding='utf-8') as f:
                    cache_data = json.load(f)
                
                original_count = len(cache_data)
                current_time = datetime.now()
                
                # 过滤过期条目
                valid_entries = {}
                for key, entry in cache_data.items():
                    try:
                        cache_time = datetime.fromisoformat(entry.get('timestamp', ''))
                        if current_time - cache_time <= timedelta(days=self.cache_duration_days):
                            valid_entries[key] = entry
                    except Exception:
                        # 无法解析时间，视为无效
                        continue
                
                # 如果有过期条目被移除，更新缓存
                if len(valid_entries) < original_count:
                    with open(self.version_cache_file, 'w', encoding='utf-8') as f:
                        json.dump(valid_entries, f, indent=2, ensure_ascii=False)
                    
                    removed_count = original_count - len(valid_entries)
                    logging.info(f"清理了{removed_count}个过期缓存条目")
                    return removed_count
                
                return 0
            except Exception as e:
                logging.error(f"清理过期缓存失败: {e}")
                self.stats['cache_errors'] += 1
                return 0
    
    def get_stats(self):
        """获取缓存统计信息
        
        Returns:
            dict: 统计信息字典
        """
        with QMutexLocker(self._mutex):
            return self.stats.copy()  # 返回副本以避免并发问题
    
    def _scan_windows_registry(self):
        """扫描Windows注册表查找Python安装
        
        通过查询Windows注册表中的Python安装信息，
        获取官方Python和其他通过MSI安装的Python版本。
        
        Returns:
            list: 从注册表找到的Python可执行文件路径列表
        """
        python_paths = []
        
        try:
            import winreg
            
            # 定义要查询的注册表路径
            registry_paths = [
                r"SOFTWARE\Python\PythonCore",  # 官方Python
                r"SOFTWARE\WOW6432Node\Python\PythonCore"  # 32位Python在64位系统上
            ]
            
            # 定义要查询的根键
            root_keys = [
                (winreg.HKEY_LOCAL_MACHINE, "HKEY_LOCAL_MACHINE"),
                (winreg.HKEY_CURRENT_USER, "HKEY_CURRENT_USER")
            ]
            
            for root_key, root_name in root_keys:
                for reg_path in registry_paths:
                    try:
                        # 打开注册表键
                        with winreg.OpenKey(root_key, reg_path) as key:
                            # 枚举所有子键（Python版本）
                            i = 0
                            while True:
                                try:
                                    version = winreg.EnumKey(key, i)
                                    i += 1
                                    
                                    # 构建完整路径
                                    version_path = f"{reg_path}\\{version}\\InstallPath"
                                    
                                    try:
                                        # 获取安装路径
                                        with winreg.OpenKey(root_key, version_path) as install_key:
                                            install_path, _ = winreg.QueryValueEx(install_key, "")
                                            
                                            # 验证路径是否存在
                                            if os.path.exists(install_path):
                                                python_exe = os.path.join(install_path, "python.exe")
                                                if os.path.isfile(python_exe):
                                                    python_paths.append(python_exe)
                                                    print(f"🔍 从{root_name}注册表找到Python {version}: {python_exe}")
                                                
                                                # 检查Scripts目录
                                                scripts_python = os.path.join(install_path, "Scripts", "python.exe")
                                                if os.path.isfile(scripts_python):
                                                    python_paths.append(scripts_python)
                                                    print(f"🔍 从{root_name}注册表找到Python Scripts {version}: {scripts_python}")
                                                
                                    except (OSError, WindowsError):
                                        # 某些版本可能没有InstallPath键
                                        continue
                                        
                                except OSError:
                                    # 枚举完成
                                    break
                                    
                    except (OSError, WindowsError):
                        # 注册表路径不存在，跳过
                        continue
                        
        except ImportError:
            print("⚠ 无法导入winreg模块，跳过Windows注册表扫描")
        except Exception as e:
            print(f"⚠ 扫描Windows注册表时出错: {e}")
        
        # 去重并返回
        return list(set(python_paths))


class ThreadManager:
    """线程管理器 - 统一管理所有后台线程，避免资源竞争"""
    def __init__(self):
        self.active_threads = {}
        self.thread_lock = QMutex()
        self.max_concurrent_threads = 3  # 最大并发线程数
        
    def create_thread(self, thread_class, thread_id, *args, **kwargs):
        """创建并管理线程"""
        with QMutexLocker(self.thread_lock):
            # 检查并发线程数量
            active_count = len([t for t in self.active_threads.values() if t.isRunning()])
            if active_count >= self.max_concurrent_threads:
                print(f"警告: 达到最大并发线程数 {self.max_concurrent_threads}, 等待其他线程完成")
                
            # 清理已完成的线程
            self._cleanup_finished_threads()
            
            # 创建新线程
            thread = thread_class(*args, **kwargs)
            thread.finished.connect(lambda: self._on_thread_finished(thread_id))
            
            self.active_threads[thread_id] = thread
            return thread
            
    def _cleanup_finished_threads(self):
        """清理已完成的线程"""
        finished_threads = []
        for thread_id, thread in self.active_threads.items():
            if not thread.isRunning() and thread.isFinished():
                finished_threads.append(thread_id)
                
        for thread_id in finished_threads:
            del self.active_threads[thread_id]
            
    def _on_thread_finished(self, thread_id):
        """线程完成回调"""
        with QMutexLocker(self.thread_lock):
            if thread_id in self.active_threads:
                thread = self.active_threads[thread_id]
                if thread.isFinished():
                    del self.active_threads[thread_id]
                    
    def cancel_all_threads(self):
        """取消所有线程"""
        with QMutexLocker(self.thread_lock):
            for thread in self.active_threads.values():
                if hasattr(thread, 'cancel'):
                    thread.cancel()
                if thread.isRunning():
                    thread.quit()
                    thread.wait(1000)  # 等待1秒
                    
    def get_active_thread_count(self):
        """获取活跃线程数量"""
        with QMutexLocker(self.thread_lock):
            return len([t for t in self.active_threads.values() if t.isRunning()])
    
    def get_thread(self, thread_id):
        """获取指定ID的线程
        
        Args:
            thread_id (str): 线程ID
            
        Returns:
            QThread: 线程对象，如果不存在则返回None
        """
        with QMutexLocker(self.thread_lock):
            return self.active_threads.get(thread_id)
    
    def start_thread(self, thread_id):
        """启动指定ID的线程
        
        Args:
            thread_id (str): 线程ID
        """
        with QMutexLocker(self.thread_lock):
            thread = self.active_threads.get(thread_id)
            if thread and not thread.isRunning():
                thread.start()


class VersionCheckThread(QThread):
    """版本检测后台线程
    
    将耗时的Python和Nuitka版本检测操作移到后台线程执行，
    避免阻塞UI主线程，提升用户体验。
    支持缓存机制，优先使用缓存数据。
    """
    # 定义信号
    version_check_completed = Signal(str, str)  # 版本检测完成信号（Python版本，Nuitka版本）
    cache_hit = Signal(str, str)  # 缓存命中信号（Python版本，Nuitka版本）
    
    def __init__(self, python_cmd, use_cache=True, parent=None):
        super().__init__(parent)
        self.python_cmd = python_cmd
        self.use_cache = use_cache
        self._canceled = False
        self.cache_manager = CacheManager() if use_cache else None
        
    def run(self):
        """线程主执行方法"""
        try:
            # 如果启用缓存，先尝试从缓存获取
            if self.use_cache and self.cache_manager:
                cached_python, cached_nuitka = self.cache_manager.get_cached_versions(self.python_cmd)
                if cached_python is not None or cached_nuitka is not None:
                    # 缓存命中，直接返回缓存数据
                    self.cache_hit.emit(cached_python, cached_nuitka)
                    return
            
            # 缓存未命中或禁用缓存，执行实际检测
            python_version = self._get_python_version()
            nuitka_version = self._get_nuitka_version()
            
            # 保存到缓存
            if self.use_cache and self.cache_manager and not self._canceled:
                self.cache_manager.save_cached_versions(self.python_cmd, python_version, nuitka_version)
            
            if not self._canceled:
                self.version_check_completed.emit(python_version, nuitka_version)
        except Exception as e:
            if not self._canceled:
                self.version_check_completed.emit(None, None)
    
    def cancel(self):
        """取消检测"""
        self._canceled = True
    
    def _get_python_version(self):
        """获取Python版本信息"""
        try:
            # 首先检查是否有缓存的Python版本信息
            if hasattr(self, '_cached_python_version') and self._cached_python_version:
                return self._cached_python_version
                
            # Windows平台特殊处理，隐藏命令行窗口
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            # 执行python --version命令获取版本信息
            result = subprocess.run(
                [self.python_cmd, "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                startupinfo=startupinfo,
                shell=False
            )
            
            if result.returncode == 0:
                version = result.stdout.strip() or result.stderr.strip()
                if version.startswith("Python "):
                    version = version[7:]  # 去除"Python "前缀
                
                # 缓存结果到内存
                self._cached_python_version = version
                return version
            
        except Exception:
            pass
        
        return None
    
    def _get_nuitka_version(self):
        """获取Nuitka版本信息"""
        try:
            # 首先检查是否有缓存的Nuitka版本信息
            if hasattr(self, '_cached_nuitka_version') and self._cached_nuitka_version:
                return self._cached_nuitka_version
                
            # Windows平台特殊处理，隐藏命令行窗口
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            # 执行python -m nuitka --version命令获取版本信息
            result = subprocess.run(
                [self.python_cmd, "-m", "nuitka", "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                startupinfo=startupinfo,
                shell=False
            )
            
            if result.returncode == 0:
                version = result.stdout.strip()
                # 清理版本信息，去除多余信息
                if "Nuitka" in version:
                    version = version.replace("Nuitka ", "").strip()
                if version.startswith("v") or version.startswith("V"):
                    version = version[1:].strip()
                
                # 缓存结果到内存
                self._cached_nuitka_version = version
                return version
            
        except Exception:
            pass
        
        return None


class NuitkaDetectionThread(QThread):
    """Nuitka安装检测后台线程
    
    将耗时的Nuitka安装检测操作移到后台线程执行，
    避免阻塞UI主线程，提升用户体验。
    """
    # 定义信号
    detection_started = Signal()       # 检测开始信号
    detection_completed = Signal(bool)  # 检测完成信号（是否安装成功）
    detection_failed = Signal(str)     # 检测失败信号（错误信息）
    log_message = Signal(str, str)     # 日志消息信号（消息，类型）
    
    # 类级别内存缓存，避免重复检测
    _detection_cache = {}
    _cache_timestamp = {}
    _cache_timeout = 300  # 缓存超时时间（秒）
    
    def __init__(self, python_cmd, force=False, parent=None):
        super().__init__(parent)
        self.python_cmd = python_cmd
        self.force = force
        self._canceled = False
        
    def run(self):
        """线程主执行方法"""
        # 发出检测开始信号
        self.detection_started.emit()
        
        try:
            # 执行Nuitka安装检测
            result = self._perform_nuitka_detection()
            
            if not self._canceled:
                self.detection_completed.emit(result)
        except Exception as e:
            if not self._canceled:
                self.detection_failed.emit(str(e))
    
    def cancel(self):
        """取消检测"""
        self._canceled = True
    
    def _perform_nuitka_detection(self):
        """执行Nuitka安装检测
        
        Returns:
            bool: 是否检测到Nuitka安装
        """
        import time
        from datetime import datetime
        
        # 记录开始时间用于性能监控
        start_time = time.time()
        
        # 检查是否使用缓存并且缓存有效
        if not self.force:
            # 清理过期缓存
            current_time = time.time()
            for cmd, timestamp in list(self._cache_timestamp.items()):
                if current_time - timestamp > self._cache_timeout:
                    if cmd in self._detection_cache:
                        del self._detection_cache[cmd]
                    if cmd in self._cache_timestamp:
                        del self._cache_timestamp[cmd]
            
            # 检查是否有缓存的检测结果
            if self.python_cmd in self._detection_cache:
                self.log_message.emit(f"✓ 使用内存缓存的Nuitka检测结果\n", "success")
                return self._detection_cache[self.python_cmd]
        else:
            self.log_message.emit("⚠ 强制重新检测，忽略内存缓存\n", "warning")
            
        # 添加调试信息
        self.log_message.emit(f"开始执行Nuitka检测，使用Python命令: {self.python_cmd}\n", "info")
        
        try:
            # Windows平台特殊处理，隐藏命令行窗口
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            # 直接使用用户选择的Python解释器执行 nuitka --version
            self.log_message.emit(f"执行命令: {self.python_cmd} -m nuitka --version\n", "info")
            result = subprocess.run(
                [self.python_cmd, "-m", "nuitka", "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                startupinfo=startupinfo,
                shell=False
            )
            self.log_message.emit(f"命令执行完成，返回码: {result.returncode}\n", "info")
            
            # 如果python -m nuitka失败，检查是否是conda环境，尝试使用conda run
            if result.returncode != 0:
                conda_env_name = self._get_conda_env_name(self.python_cmd)
                if conda_env_name:
                    try:
                        self.log_message.emit(f"检测到conda环境 '{conda_env_name}'，尝试使用conda run...\n", "info")
                        
                        # 查找conda的完整路径
                        conda_paths = []
                        possible_paths = [
                            os.path.join(os.path.dirname(self.python_cmd), "..", "..", "condabin", "conda.bat"),
                            os.path.join(os.path.dirname(self.python_cmd), "..", "..", "condabin", "conda"),
                            os.path.join(os.path.dirname(self.python_cmd), "..", "..", "Scripts", "conda.exe"),
                            "conda",
                            "mamba"
                        ]
                        
                        for path in possible_paths:
                            if os.path.exists(path):
                                conda_paths.append(path)
                        
                        # 尝试使用找到的conda路径
                        success = False
                        for conda_cmd in conda_paths:
                            try:
                                self.log_message.emit(f"尝试使用conda命令: {conda_cmd}\n", "info")
                                result = subprocess.run(
                                    [conda_cmd, "run", "-n", conda_env_name, "nuitka", "--version"],
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE,
                                    text=True,
                                    startupinfo=startupinfo,
                                    shell=False
                                )
                                if result.returncode == 0:
                                    success = True
                                    break
                                else:
                                    self.log_message.emit(f"使用 {conda_cmd} 失败，返回码: {result.returncode}\n", "warning")
                                    self.log_message.emit(f"错误输出: {result.stderr}\n", "warning")
                            except Exception as path_error:
                                self.log_message.emit(f"使用 {conda_cmd} 失败: {str(path_error)}\n", "warning")
                        
                        if not success:
                            raise Exception(f"所有conda命令尝试均失败，尝试的路径: {conda_paths}")
                        
                    except Exception as conda_error:
                        self.log_message.emit(f"conda run失败: {str(conda_error)}\n", "warning")
            
            # 处理检测结果
            if result.returncode == 0:
                version = result.stdout.strip()
                # 清理版本信息，去除多余信息
                if "Nuitka" in version:
                    version = version.replace("Nuitka ", "").strip()
                if version.startswith("v") or version.startswith("V"):
                    version = version[1:].strip()
                
                # 验证版本信息是否有效
                if version and version != "unknown":
                    self.log_message.emit(f"✓ 检测到Nuitka版本: {version}\n", "success")
                    # 缓存结果到内存
                    self._detection_cache[self.python_cmd] = True
                    self._cache_timestamp[self.python_cmd] = time.time()
                    return True
                else:
                    raise Exception("无法解析版本信息")
            else:
                raise Exception("命令行检测失败")
                
        except Exception as e:
            # 处理检测失败的情况
            self.log_message.emit(f"⚠ 未检测到Nuitka: {str(e)}\n", "warning")
            
            # 只在强制检测时显示完整的安装指南
            if self.force:
                self.log_message.emit("请使用以下命令安装Nuitka：\n", "info")
                self.log_message.emit("# 使用pip安装 (推荐)\n", "info")
                self.log_message.emit("nuitka稳定版 pip install nuitka\n", "info")
                self.log_message.emit("nuitka测试版 pip install -U https://github.com/Nuitka/Nuitka/archive/develop.zip \n", "info")
                self.log_message.emit("# 使用conda安装\n", "info")
                self.log_message.emit("conda install -c conda-forge nuitka\n", "info")
                self.log_message.emit("# 使用mamba安装 (更快)\n", "info")
                self.log_message.emit("mamba install -c conda-forge nuitka\n", "info")
                self.log_message.emit("# 升级到最新版本\n", "info")
                self.log_message.emit("pip install --upgrade nuitka\n", "info")
            
            # 缓存结果到内存
            self._detection_cache[self.python_cmd] = False
            self._cache_timestamp[self.python_cmd] = time.time()
            return False
    
    def _get_conda_env_name(self, python_cmd):
        """获取conda环境名称
        
        Args:
            python_cmd (str): Python可执行文件路径
            
        Returns:
            str: conda环境名称，如果不是conda环境则返回None
        """
        try:
            python_dir = os.path.dirname(python_cmd)
            parent_dir = os.path.dirname(python_dir)
            parent_name = os.path.basename(parent_dir)
            
            # 如果Python路径在envs目录下，说明是conda环境
            if parent_name == "envs":
                return os.path.basename(python_dir)
            
            # 检查是否在conda的base环境中
            conda_meta_path = os.path.join(python_dir, "conda-meta")
            if os.path.exists(conda_meta_path):
                return "base"
                
        except Exception:
            pass
        
        return None


class DependencyScanThread(QThread):
    """依赖扫描后台线程
    
    将耗时的项目依赖扫描操作移到后台线程执行，
    避免阻塞UI主线程，提升用户体验。
    """
    # 定义信号
    scan_completed = Signal(list)     # 扫描完成信号（依赖模块列表）
    scan_failed = Signal(str)        # 扫描失败信号（错误信息）
    progress_updated = Signal(int, str)  # 进度更新信号（进度值，消息）
    log_message = Signal(str, str)   # 日志消息信号（消息，类型）
    
    def __init__(self, script_path, parent=None):
        super().__init__(parent)
        self.script_path = script_path
        self._canceled = False
        
    def run(self):
        """线程主执行方法"""
        try:
            # 执行依赖扫描
            custom_modules = self._perform_dependency_scan()
            
            if not self._canceled:
                self.scan_completed.emit(custom_modules)
        except Exception as e:
            if not self._canceled:
                self.scan_failed.emit(str(e))
    
    def cancel(self):
        """取消扫描"""
        self._canceled = True
    
    def _perform_dependency_scan(self):
        """执行依赖扫描
        
        Returns:
            list: 找到的外部依赖模块列表
        """
        try:
            self.progress_updated.emit(10, "初始化依赖扫描...")
            self.log_message.emit("\n🔍 开始扫描项目依赖...\n", "info")
            
            # 检查脚本路径是否存在
            if not os.path.exists(self.script_path):
                raise FileNotFoundError(f"脚本文件不存在: {self.script_path}")
            
            # 使用替代方法分析导入（不使用modulefinder）
            try:
                # 创建自定义的依赖扫描器
                class CustomDependencyScanner:
                    def __init__(self):
                        self.modules = {}
                        self.imported_modules = set()
                    
                    def run_script(self, script_path):
                        """分析脚本文件中的导入"""
                        if not os.path.exists(script_path):
                            raise FileNotFoundError(f"脚本文件不存在: {script_path}")
                        
                        try:
                            with open(script_path, 'r', encoding='utf-8') as f:
                                content = f.read()
                            
                            # 使用正则表达式查找import语句
                            import re
                            
                            # 匹配 import module
                            import_pattern = r'^\s*import\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)*)'
                            # 匹配 from module import name
                            from_pattern = r'^\s*from\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)*)\s+import'
                            
                            lines = content.split('\n')
                            for line in lines:
                                # 跳过注释行
                                line = line.strip()
                                if line.startswith('#'):
                                    continue
                                
                                # 查找import语句
                                match = re.match(import_pattern, line)
                                if match:
                                    module_name = match.group(1).split('.')[0]
                                    self.imported_modules.add(module_name)
                                    continue
                                
                                # 查找from...import语句
                                match = re.match(from_pattern, line)
                                if match:
                                    module_name = match.group(1).split('.')[0]
                                    self.imported_modules.add(module_name)
                            
                            # 创建模拟的模块对象
                            for module_name in self.imported_modules:
                                # 创建一个简单的模拟模块对象
                                class MockModule:
                                    def __init__(self, name):
                                        self.__name__ = name
                                        self.__file__ = None  # 我们会在后面检查
                                        self.is_package = False
                                
                                self.modules[module_name] = MockModule(module_name)
                                
                        except Exception as e:
                            raise RuntimeError(f"分析脚本失败: {str(e)}")
                
                finder = CustomDependencyScanner()
            except Exception as e:
                raise RuntimeError(f"初始化依赖扫描器失败: {str(e)}")
                
            self.progress_updated.emit(20, "正在分析脚本...")
            
            try:
                finder.run_script(self.script_path)
            except Exception as e:
                raise RuntimeError(f"分析脚本失败: {str(e)}")
            
            if self._canceled:
                return []
            
            self.progress_updated.emit(40, "正在识别模块...")
            
            # 获取所有非标准库模块
            custom_modules = []
            stdlib_path = os.path.dirname(os.__file__)
            script_dir = os.path.dirname(os.path.abspath(self.script_path))
            
            # 遍历所有找到的模块
            total_modules = len(finder.modules)
            for i, (name, module) in enumerate(finder.modules.items()):
                if self._canceled:
                    return []
                
                # 更新进度
                progress = 40 + int(60 * i / total_modules)
                self.progress_updated.emit(progress, f"正在处理模块: {name}")
                
                # 跳过内置模块和特殊模块
                if name in ['sys', 'builtins', '__main__', '__future__', 'os', 're']:
                    continue
                    
                # 检查module对象是否有效
                if module is None:
                    self.log_message.emit(f"⚠ 跳过空模块: {name}\n", "warning")
                    continue
                    
                # 检查module对象是否有必要的属性
                if not hasattr(module, '__name__'):
                    self.log_message.emit(f"⚠ 跳过缺少属性的模块: {name}\n", "warning")
                    continue
                    
                # 检查module对象是否有is_package属性
                if not hasattr(module, 'is_package'):
                    self.log_message.emit(f"⚠ 跳过缺少is_package属性的模块: {name}\n", "warning")
                    continue
                
                # 尝试导入模块以检查其是否为标准库模块
                try:
                    import importlib
                    import sys
                    
                    # 尝试导入模块
                    imported_module = importlib.import_module(name)
                    
                    # 检查模块是否在标准库中
                    module_file = getattr(imported_module, '__file__', None)
                    if module_file and stdlib_path in os.path.abspath(module_file):
                        continue
                        
                    # 跳过主脚本自身
                    if module_file and os.path.abspath(module_file) == os.path.abspath(self.script_path):
                        continue
                        
                    # 跳过在脚本目录下的模块（可能是项目本地模块）
                    if module_file and script_dir in os.path.abspath(module_file):
                        continue
                        
                    # 将外部模块添加到列表中
                    custom_modules.append(name)
                    self.log_message.emit(f"✓ 找到外部依赖: {name}\n", "success")
                    
                except ImportError:
                    # 模块无法导入，可能是第三方模块但未安装
                    custom_modules.append(name)
                    self.log_message.emit(f"✓ 找到可能的外部依赖: {name} (未安装)\n", "warning")
                except Exception as e:
                    self.log_message.emit(f"⚠ 处理模块 {name} 时出错: {str(e)}\n", "warning")
                    continue
            
            self.progress_updated.emit(100, "依赖扫描完成")
            self.log_message.emit("依赖扫描完成\n", "success")
            
            return list(set(custom_modules))  # 去重
            
        except Exception as e:
            self.log_message.emit(f"⛔ 依赖扫描失败: {str(e)}\n", "error")
            raise


class PythonDetectionThread(QThread):
    """Python环境检测后台线程类
    
    负责在后台线程中检测系统中安装的Python环境，支持以下功能：
    - 从缓存中快速获取Python路径信息
    - 检测环境变量中配置的Python
    - 扫描PATH环境变量中的Python可执行文件
    - 在Windows系统中扫描注册表获取Python安装信息
    - 支持取消操作和超时控制
    - 提供详细的日志和进度报告
    """
    
    # 定义信号
    detection_started = Signal()           # 检测开始信号
    detection_progress = Signal(str, int)  # 检测进度信号（消息，进度百分比）
    detection_completed = Signal(list, bool)  # 检测完成信号，传递Python路径列表和是否来自缓存
    detection_failed = Signal(str)         # 检测失败信号，传递错误信息
    progress_updated = Signal(int, str)    # 进度更新信号
    log_message = Signal(str, str)         # 日志消息信号
    
    def __init__(self, parent=None, silent=True, force=False, timeout=30):
        """初始化Python检测线程
        
        Args:
            parent: 父对象
            silent: 是否静默模式
            force: 是否强制重新检测，忽略缓存
            timeout: 检测超时时间（秒），0表示不超时
        """
        super().__init__(parent)
        self._is_running = True
        self.detection_count = 0
        self.silent = silent
        self.force = force
        self.timeout = timeout
        self._start_time = None
        self.cache_manager = CacheManager()
        self._mutex = QMutex()
        
    def run(self):
        """执行Python环境检测"""
        try:
            # 记录开始时间
            self._start_time = time.time()
            
            # 发送检测开始信号
            self.detection_started.emit()
            self.progress_updated.emit(0, "准备检测环境...")
            
            # 如果不是强制检测，先尝试从缓存获取
            if not self.force:
                cached_paths = self.cache_manager.get_cached_python_paths()
                logging.debug(f"缓存检查结果: {cached_paths}")
                self.log_message.emit(f"🔍 缓存检查结果: {'找到' if cached_paths else '未找到'}", "info")
                
                if cached_paths:
                    logging.info("使用缓存的Python环境信息")
                    self.log_message.emit("✅ 使用缓存的Python环境信息", "success")
                    self.progress_updated.emit(100, "检测完成")
                    self.detection_completed.emit(cached_paths, True)  # True表示来自缓存
                    return
            else:
                logging.info("强制重新检测Python环境，忽略缓存")
                self.log_message.emit("🔄 强制重新检测Python环境，忽略缓存", "info")
            
            # 缓存未命中或强制检测，执行实际检测
            self.progress_updated.emit(10, "开始执行检测...")
            python_paths = self._perform_full_python_detection()
            
            # 检查是否取消或超时
            if not self._is_running or self._check_timeout():
                logging.info("检测被取消或超时")
                return
            
            # 去重处理
            python_paths = list(set(python_paths))
            python_paths.sort(key=lambda x: len(x))  # 按路径长度排序
            
            # 发送完成信号
            self.progress_updated.emit(100, "检测完成")
            self.detection_completed.emit(python_paths, False)  # False表示不是来自缓存
                
        except Exception as e:
            error_msg = f"Python环境检测失败: {str(e)}"
            logging.error(error_msg)
            self.log_message.emit(f"❌ {error_msg}", "error")
            self.detection_failed.emit(error_msg)
    
    def _simple_python_detection(self):
        """简化的Python检测方法，作为备用方案"""
        python_paths = []
        
        try:
            # 检查PATH环境变量中的Python
            path_env = os.environ.get('PATH', '')
            paths = path_env.split(os.pathsep)
            python_names = ['python.exe', 'python3.exe', 'python39.exe', 'python310.exe', 'python311.exe', 'python312.exe']
            
            logging.info("使用简化检测逻辑搜索Python...")
            self.log_message.emit("🔍 使用简化检测逻辑搜索Python...\n", "info")
            
            for path in paths:
                if not self._is_running or self._check_timeout():
                    logging.debug("检测已取消或超时")
                    break
                    
                for name in python_names:
                    full_path = os.path.join(path, name)
                    if os.path.isfile(full_path) and full_path not in python_paths:
                        python_paths.append(full_path)
                        logging.debug(f"找到Python: {full_path}")
                        self.log_message.emit(f"✓ 找到Python: {full_path}\n", "success")
            
            # 检查常见的Python安装目录
            common_paths = [
                os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Python'),
                os.path.join(os.environ.get('PROGRAMFILES', ''), 'Python'),
                os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Python')
            ]
            
            for base_path in common_paths:
                if not self._is_running or self._check_timeout():
                    break
                    
                if os.path.exists(base_path):
                    for item in os.listdir(base_path):
                        if not self._is_running or self._check_timeout():
                            break
                            
                        item_path = os.path.join(base_path, item)
                        if os.path.isdir(item_path):
                            python_exe = os.path.join(item_path, 'python.exe')
                            if os.path.isfile(python_exe) and python_exe not in python_paths:
                                python_paths.append(python_exe)
                                logging.debug(f"从安装目录找到Python: {python_exe}")
                                self.log_message.emit(f"✓ 从安装目录找到Python: {python_exe}\n", "success")
            
            # 检查conda环境
            conda_envs = []
            for env_var in ['CONDA_PREFIX', 'CONDA_HOME']:
                if not self._is_running or self._check_timeout():
                    break
                    
                if env_var in os.environ:
                    conda_path = os.environ[env_var]
                    if env_var == 'CONDA_PREFIX':
                        python_exe = os.path.join(conda_path, 'python.exe')
                        if os.path.isfile(python_exe) and python_exe not in python_paths:
                            python_paths.append(python_exe)
                            logging.debug(f"从Conda环境找到Python: {python_exe}")
                            self.log_message.emit(f"✓ 从Conda环境找到Python: {python_exe}\n", "success")
            
        except Exception as e:
            error_msg = f"简化检测过程中出现错误: {str(e)}"
            logging.error(error_msg)
            self.log_message.emit(f"⚠ {error_msg}\n", "error")
        
        return python_paths
    
    def stop(self):
        """停止检测"""
        try:
            with QMutexLocker(self._mutex):
                self._is_running = False
                stop_msg = "Python环境检测已停止"
                logging.info(stop_msg)
                self.log_message.emit(f"🛑 {stop_msg}", "info")
                # 确保UI有机会更新
                QCoreApplication.processEvents()
        except Exception as e:
            error_msg = f"停止检测时发生错误: {str(e)}"
            logging.error(error_msg)
            self.log_message.emit(f"❌ {error_msg}", "error")
    
    def _check_timeout(self):
        """检查是否超时
        
        Returns:
            bool: 如果超时返回True，否则返回False
        """
        try:
            if self.timeout > 0 and self._start_time:
                elapsed = time.time() - self._start_time
                if elapsed > self.timeout:
                    timeout_msg = f"Python环境检测超时 ({elapsed:.2f}秒 > {self.timeout}秒)"
                    logging.warning(timeout_msg)
                    self.log_message.emit(f"⏰ {timeout_msg}", "warning")
                    self.stop()
                    return True
            return False
        except Exception as e:
            logging.error(f"检查超时发生错误: {str(e)}")
            return False
        
    def cancel(self):
        """取消检测（与其他线程类保持一致的接口）"""
        self.stop()
    
    def _add_python_path(self, python_exe, paths_list, message_prefix=""):
        """辅助方法：添加Python路径到结果列表（带重复检查）
        
        Args:
            python_exe (str): Python可执行文件路径
            paths_list (list): 要添加到的路径列表
            message_prefix (str): 日志消息前缀
            
        Returns:
            bool: 如果成功添加返回True，否则返回False
        """
        if os.path.isfile(python_exe) and python_exe not in paths_list:
            paths_list.append(python_exe)
            self.log_message.emit(f"✓ {message_prefix}: {python_exe}\n", "success")
            return True
        return False
    
    def _scan_directory_for_python(self, directory, paths_list, message_prefix="找到Python", recursive=False):
        """扫描目录中的Python可执行文件
        
        Args:
            directory (str): 要扫描的目录
            paths_list (list): 要添加到的路径列表
            message_prefix (str): 日志消息前缀
            recursive (bool): 是否递归扫描
            
        Returns:
            int: 找到的Python可执行文件数量
        """
        if not os.path.exists(directory):
            return 0
            
        import glob
        found_count = 0
        
        try:
            # 构建搜索模式
            if recursive:
                pattern = os.path.join(directory, '**', 'python.exe')
                for python_exe in glob.glob(pattern, recursive=True):
                    # 检查是否取消或超时
                    if not self._is_running or self._check_timeout():
                        break
                        
                    if self._add_python_path(python_exe, paths_list, message_prefix):
                        found_count += 1
            else:
                # 直接扫描顶级目录
                for item in os.listdir(directory):
                    # 检查是否取消或超时
                    if not self._is_running or self._check_timeout():
                        break
                        
                    item_path = os.path.join(directory, item)
                    if os.path.isdir(item_path):
                        python_exe = os.path.join(item_path, 'python.exe')
                        if self._add_python_path(python_exe, paths_list, message_prefix):
                            found_count += 1
        except Exception as e:
            self.log_message.emit(f"⚠ 扫描目录失败 {directory}: {e}\n", "warning")
            
        return found_count
    
    def _detect_environments_combined(self):
        """综合环境检测方法 - 替代多个重复的检测方法
        
        整合了conda环境检测、虚拟环境检测和常规Python检测的功能，
        避免重复代码并提供更一致的检测逻辑。
        
        Returns:
            dict: 包含不同类型环境的Python路径字典
        """
        result = {
            'conda_paths': [],
            'venv_paths': [],
            'regular_paths': []
        }
        
        # 1. 检测conda/miniconda/miniforge环境
        self.log_message.emit("🔍 开始检测Conda相关环境...\n", "info")
        
        # 常见的conda安装路径
        conda_install_paths = [
            os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Anaconda3'),
            os.path.join(os.environ.get('PROGRAMFILES', ''), 'Anaconda3'),
            os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Anaconda3'),
            os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniconda3'),
            os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniconda3'),
            os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniconda3'),
            os.path.join(os.path.expanduser('~'), 'anaconda3'),
            os.path.join(os.path.expanduser('~'), 'miniconda3'),
            os.path.join(os.path.expanduser('~'), 'miniforge3'),
            'F:\\itsoft\\miniforge3',
            'C:\\ProgramData\\Anaconda3',
            'C:\\ProgramData\\Miniconda3'
        ]
        
        # 从环境变量获取conda信息
        conda_prefix = os.environ.get('CONDA_PREFIX', '')
        conda_home = os.environ.get('CONDA_HOME', '')
        
        # 添加环境变量中的conda路径
        if conda_prefix and os.path.exists(conda_prefix) and conda_prefix not in conda_install_paths:
            conda_install_paths.append(conda_prefix)
        if conda_home and os.path.exists(conda_home) and conda_home not in conda_install_paths:
            conda_install_paths.append(conda_home)
        
        for conda_path in conda_install_paths:
            # 检查是否取消或超时
            if not self._is_running or self._check_timeout():
                break
                
            if os.path.exists(conda_path):
                # 检查基础python
                base_python = os.path.join(conda_path, 'python.exe')
                if os.path.isfile(base_python) and base_python not in result['conda_paths']:
                    result['conda_paths'].append(base_python)
                    self.log_message.emit(f"✓ 找到conda基础Python: {base_python}\n", "success")
                
                # 检查虚拟环境
                envs_dir = os.path.join(conda_path, 'envs')
                if os.path.exists(envs_dir):
                    try:
                        for env_name in os.listdir(envs_dir):
                            if not self._is_running or self._check_timeout():
                                break
                                
                            env_path = os.path.join(envs_dir, env_name)
                            if os.path.isdir(env_path):
                                python_exe = os.path.join(env_path, 'python.exe')
                                if os.path.isfile(python_exe) and python_exe not in result['conda_paths']:
                                    result['conda_paths'].append(python_exe)
                                    self.log_message.emit(f"✓ 找到conda虚拟环境 {env_name}: {python_exe}\n", "success")
                    except Exception as e:
                        self.log_message.emit(f"⚠ 扫描conda环境目录失败 {envs_dir}: {e}\n", "warning")
        
        # 2. 检测独立虚拟环境
        self.log_message.emit("🔍 开始检测独立虚拟环境...\n", "info")
        
        # 从环境变量中获取当前激活的虚拟环境
        venv_path = os.environ.get('VIRTUAL_ENV', '')
        if venv_path and os.path.exists(venv_path):
            python_exe = os.path.join(venv_path, "Scripts", "python.exe")
            if os.path.isfile(python_exe) and python_exe not in result['venv_paths']:
                result['venv_paths'].append(python_exe)
                self.log_message.emit(f"✓ 当前虚拟环境: {venv_path}\n", "success")
        
        # 检测常见的虚拟环境目录
        venv_dirs = [
            os.path.join(os.path.expanduser('~'), '.virtualenvs'),
            os.path.join(os.path.expanduser('~'), 'Envs'),
            os.path.join(os.path.expanduser('~'), '.conda', 'envs'),
            os.path.join(os.path.expanduser('~'), '.pyenv', 'pyenv-win', 'versions'),
            os.path.join(os.environ.get('WORKON_HOME', ''), '*')
        ]
        
        for venv_dir in venv_dirs:
            # 检查是否取消或超时
            if not self._is_running or self._check_timeout():
                break
                
            if os.path.exists(venv_dir):
                # 查找目录中的Python可执行文件
                try:
                    python_pattern = os.path.join(venv_dir, '**', 'python.exe')
                    for python_exe in glob.glob(python_pattern, recursive=True):
                        if not self._is_running or self._check_timeout():
                            break
                            
                        if os.path.isfile(python_exe) and python_exe not in result['venv_paths']:
                            result['venv_paths'].append(python_exe)
                            self.log_message.emit(f"✓ 找到独立虚拟环境: {python_exe}\n", "success")
                except Exception as e:
                    self.log_message.emit(f"⚠ 扫描虚拟环境目录失败 {venv_dir}: {e}\n", "warning")
        
        # 3. 检测常规Python安装
        self.log_message.emit("🔍 开始检测常规Python安装...\n", "info")
        
        # 常见的Python安装目录
        python_install_dirs = [
            os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Python'),
            os.path.join(os.environ.get('PROGRAMFILES', ''), 'Python'),
            os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Python'),
            'F:\Python',
            'C:\Python',
            'D:\Python',
            'E:\Python'
        ]
        
        for install_dir in python_install_dirs:
            # 检查是否取消或超时
            if not self._is_running or self._check_timeout():
                break
                
            if os.path.exists(install_dir):
                try:
                    # 遍历Python版本目录
                    for item in os.listdir(install_dir):
                        if not self._is_running or self._check_timeout():
                            break
                            
                        item_path = os.path.join(install_dir, item)
                        if os.path.isdir(item_path):
                            # 检查Python可执行文件
                            python_exe = os.path.join(item_path, 'python.exe')
                            if os.path.isfile(python_exe) and python_exe not in result['regular_paths']:
                                # 确保这不是conda环境
                                if 'conda' not in python_exe.lower() and 'miniconda' not in python_exe.lower() and 'miniforge' not in python_exe.lower():
                                    result['regular_paths'].append(python_exe)
                                    self.log_message.emit(f"✓ 找到常规Python安装: {python_exe}\n", "success")
                except Exception as e:
                    self.log_message.emit(f"⚠ 扫描Python安装目录失败 {install_dir}: {e}\n", "warning")
        
        return result
    
    # _detect_standalone_virtual_environments方法已被_detect_environments_combined替代
    # _detect_standalone_virtual_environments_from_env_managers方法已被_detect_environments_combined替代

    def _perform_full_python_detection(self):
        """执行完整的Python环境检测
        
        整合了所有Python环境检测方法，包括:
        - 系统环境变量检测
        - Windows注册表扫描
        - Conda/Miniconda/Miniforge环境检测
        - 独立虚拟环境检测
        
        Returns:
            list: 检测到的所有Python路径列表
        """
        import time
        import platform
        
        # 记录开始时间用于性能监控
        start_time = time.time()
        
        # 初始化结果列表
        python_paths = []
        
        self.log_message.emit("🔍 开始执行完整Python环境检测...\n", "info")
        
        # 1. 调用综合环境检测方法获取各类环境
        environments = self._detect_environments_combined()
        
        # 检查是否取消或超时
        if not self._is_running or self._check_timeout():
            return python_paths
        
        # 将检测到的各类环境Python路径添加到结果列表
        if environments.get('conda_paths'):
            python_paths.extend(environments['conda_paths'])
            self.log_message.emit(f"✅ 已收集 {len(environments['conda_paths'])} 个conda环境\n", "success")
        
        if environments.get('venv_paths'):
            python_paths.extend(environments['venv_paths'])
            self.log_message.emit(f"✅ 已收集 {len(environments['venv_paths'])} 个虚拟环境\n", "success")
        
        if environments.get('regular_paths'):
            python_paths.extend(environments['regular_paths'])
            self.log_message.emit(f"✅ 已收集 {len(environments['regular_paths'])} 个常规Python环境\n", "success")
        
        # 2. 检查系统环境变量中的Python
        # 定义需要检查的环境变量及其对应的管理器类型
        env_vars_to_check = [
            ('PYTHON_HOME', 'python'),     # Python安装目录
            ('PYTHONPATH', 'python'),      # Python模块搜索路径
            ('CONDA_PREFIX', 'conda'),     # Conda当前环境路径
            ('CONDA_HOME', 'conda'),       # Conda安装根目录
            ('MINICONDA_HOME', 'miniconda'), # Miniconda安装目录
            ('MINIFORGE_HOME', 'miniforge'), # Miniforge安装目录
            ('MAMBA_HOME', 'mamba')        # Mamba安装目录
        ]
        
        # 遍历环境变量列表，检查每个环境变量是否存在
        for env_var, manager_type in env_vars_to_check:
            if env_var in os.environ:
                env_value = os.environ[env_var]
                self.log_message.emit(f"🔍 发现环境变量 {env_var}: {env_value}\n", "info")
                
                if env_var == 'CONDA_PREFIX':
                    # CONDA_PREFIX指向的是具体环境，直接使用
                    python_exe = os.path.join(env_value, 'python.exe')
                    if os.path.isfile(python_exe) and python_exe not in python_paths:
                        python_paths.append(python_exe)
                        self.log_message.emit(f"✓ 从{env_var}找到Python: {python_exe}\n", "success")
                elif env_var == 'PYTHONPATH':
                    # PYTHONPATH是模块搜索路径，不是Python安装路径，跳过处理
                    continue
                else:
                    # 其他环境变量指向的是基础目录
                    base_path = env_value
                    # 检查基础Python可执行文件
                    python_exe = os.path.join(base_path, 'python.exe')
                    if os.path.isfile(python_exe) and python_exe not in python_paths:
                        python_paths.append(python_exe)
                        self.log_message.emit(f"✓ 从{env_var}找到Python: {python_exe}\n", "success")
        
        # 3. 检查PATH环境变量中的Python
        # 获取PATH环境变量并按路径分隔符分割
        path_env = os.environ.get('PATH', '')
        paths = path_env.split(os.pathsep)
        
        # 常见的Python可执行文件名（包括版本特定的名称）
        python_names = ['python.exe', 'python3.exe', 'python39.exe', 'python310.exe', 'python311.exe', 'python312.exe']
        
        self.log_message.emit("🔍 检查PATH环境变量中的Python...\n", "info")
        # 遍历PATH中的每个目录
        for path in paths:
            # 检查是否取消或超时
            if not self._is_running or self._check_timeout():
                break
                
            # 检查每个可能的Python可执行文件名
            for name in python_names:
                full_path = os.path.join(path, name)
                if os.path.isfile(full_path) and full_path not in python_paths:
                    python_paths.append(full_path)
                    self.log_message.emit(f"✓ 从PATH找到Python: {full_path}\n", "success")
        
        # 4. 扫描Windows注册表
        if platform.system() == 'Windows':
            self.log_message.emit("🔍 扫描Windows注册表...\n", "info")
            try:
                # 使用_cache_manager中的扫描方法或实现简单的注册表扫描
                import winreg
                registry_paths = []
                
                # 定义要查询的注册表路径
                reg_paths = [
                    r"SOFTWARE\Python\PythonCore",  # 官方Python
                    r"SOFTWARE\WOW6432Node\Python\PythonCore"  # 32位Python在64位系统上
                ]
                
                # 定义要查询的根键
                root_keys = [
                    (winreg.HKEY_LOCAL_MACHINE, "HKEY_LOCAL_MACHINE"),
                    (winreg.HKEY_CURRENT_USER, "HKEY_CURRENT_USER")
                ]
                
                for root_key, root_name in root_keys:
                    for reg_path in reg_paths:
                        try:
                            # 打开注册表键 (指定访问权限为只读)
                            with winreg.OpenKey(root_key, reg_path, 0, winreg.KEY_READ) as key:
                                # 枚举所有子键（Python版本）
                                i = 0
                                while True:
                                    try:
                                        version = winreg.EnumKey(key, i)
                                        i += 1
                                        
                                        # 构建完整路径 (使用os.path.join避免路径分隔符问题)
                                        version_path = os.path.join(reg_path, version, "InstallPath")
                                        
                                        try:
                                            # 获取安装路径 (指定访问权限为只读)
                                            with winreg.OpenKey(root_key, version_path, 0, winreg.KEY_READ) as install_key:
                                                install_path, _ = winreg.QueryValueEx(install_key, "")
                                                
                                                # 验证路径是否存在
                                                if os.path.exists(install_path):
                                                    python_exe = os.path.join(install_path, "python.exe")
                                                    if os.path.isfile(python_exe):
                                                        registry_paths.append(python_exe)
                                                        self.log_message.emit(f"✓ 从{root_name}注册表找到Python {version}: {python_exe}\n", "success")
                                                
                                        except Exception:
                                            # 某些版本可能没有InstallPath键
                                            continue
                                                
                                    except OSError:
                                        # 枚举完成
                                        break
                                            
                        except Exception:
                            # 注册表路径不存在，跳过
                            continue
                
                # 添加注册表找到的路径
                for path in registry_paths:
                    if path not in python_paths:
                        python_paths.append(path)
                
                self.log_message.emit(f"📊 注册表中发现 {len(registry_paths)} 个Python路径\n", "info")
            except Exception as e:
                self.log_message.emit(f"❌ 注册表扫描失败: {e}\n", "error")
        
        # 去重处理
        python_paths = list(set(python_paths))
        
        # 记录性能统计
        elapsed_time = time.time() - start_time
        self.log_message.emit(f"🔍 Python环境检测完成，耗时 {elapsed_time:.2f} 秒\n", "info")
        self.log_message.emit(f"📊 总共发现 {len(python_paths)} 个Python环境\n", "info")
        
        # 保存到缓存
        try:
            # 使用CacheManager保存缓存
            self.cache_manager.save_cached_python_paths(python_paths)
            cache_dir = self.cache_manager.cache_dir
            cache_file = os.path.join(cache_dir, "python_paths_cache.pkl")
            self.log_message.emit(f"✅ 检测结果已保存到缓存: {cache_file}\n", "success")
        except Exception as e:
            self.log_message.emit(f"⚠ 保存缓存失败: {e}\n", "warning")
        
        return python_paths
    
    def _get_python_version_info(self, python_path):
        """获取Python版本信息（新方法）"""
        try:
            result = subprocess.run(
                [python_path, "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                version = result.stdout.strip().replace("Python ", "")
                
                # 获取架构信息
                arch_result = subprocess.run(
                    [python_path, "-c", "import platform; print(platform.architecture()[0])"],
                    capture_output=True,
                    text=True,
                    timeout=10
                )
                architecture = arch_result.stdout.strip() if arch_result.returncode == 0 else "unknown"
                
                return {"version": version, "architecture": architecture}
        except Exception as e:
            self.log_message.emit(f"⚠ 获取版本失败 {python_path}: {e}\n", "warning")
        return None
    
    # 重复的环境检测方法已被整合到_detect_environments_combined和_perform_full_python_detection方法中
    
    def _detect_conda_environments(self):
        """检测conda环境
        
        Returns:
            list: 检测到的conda环境中的Python路径列表
        """
        conda_paths = []
        
        # 常见的conda安装路径
        conda_install_paths = [
            os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Anaconda3'),
            os.path.join(os.environ.get('PROGRAMFILES', ''), 'Anaconda3'),
            os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Anaconda3'),
            os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniconda3'),
            os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniconda3'),
            os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniconda3'),
            os.path.join(os.path.expanduser('~'), 'anaconda3'),
            os.path.join(os.path.expanduser('~'), 'miniconda3'),
            os.path.join(os.path.expanduser('~'), 'miniforge3'),

        ]
        
        for conda_path in conda_install_paths:
            if os.path.exists(conda_path):
                # 检查base环境
                base_python = os.path.join(conda_path, 'python.exe')
                if os.path.isfile(base_python):
                    conda_paths.append(base_python)
                    self.log_message.emit(f"✓ 从conda base环境找到Python: {base_python}\n", "success")
                
                # 检查envs目录下的环境
                envs_dir = os.path.join(conda_path, 'envs')
                if os.path.exists(envs_dir):
                    for env_name in os.listdir(envs_dir):
                        env_path = os.path.join(envs_dir, env_name)
                        if os.path.isdir(env_path):
                            env_python = os.path.join(env_path, 'python.exe')
                            if os.path.isfile(env_python):
                                conda_paths.append(env_python)
                                self.log_message.emit(f"✓ 从conda环境 {env_name} 找到Python: {env_python}\n", "success")
        
        return conda_paths
    
    def _detect_standalone_virtual_environments(self):
        """检测独立的虚拟环境
        
        Returns:
            list: 检测到的虚拟环境中的Python路径列表
        """
        venv_paths = []
        
        # 常见的虚拟环境目录
        venv_dirs = [
            os.path.join(os.path.expanduser('~'), 'venv'),
            os.path.join(os.path.expanduser('~'), 'env'),
            os.path.join(os.path.expanduser('~'), '.venv'),
            os.path.join(os.path.expanduser('~'), 'virtualenvs'),
            'F:\\venv',
            'C:\\venv',
            'D:\\venv',
            'E:\\venv'
        ]
        
        for venv_dir in venv_dirs:
            if os.path.exists(venv_dir):
                # 检查Scripts目录下的python.exe
                python_exe = os.path.join(venv_dir, 'Scripts', 'python.exe')
                if os.path.isfile(python_exe):
                    venv_paths.append(python_exe)
                    self.log_message.emit(f"✓ 从虚拟环境找到Python: {python_exe}\n", "success")
        
        return venv_paths
    
    def _detect_virtual_environments_from_python_paths(self, python_paths):
        """基于已找到的Python路径检测虚拟环境
        
        Args:
            python_paths (list): 已找到的Python路径列表
        """
        import glob
        
        self.log_message.emit("🔍 基于Python路径检测虚拟环境...\n", "info")
        
        # 遍历已找到的Python路径
        for python_path in python_paths:
            if not self._is_running:
                return
                
            # 获取Python路径的目录部分
            python_dir = os.path.dirname(python_path)
            
            # 检查是否在conda环境中
            if 'envs' in python_path:
                # 提取conda基础目录
                conda_base = python_path.split('envs')[0]
                if conda_base and os.path.exists(conda_base):
                    # 检查conda基础目录下的envs目录
                    envs_dir = os.path.join(conda_base, 'envs')
                    if os.path.exists(envs_dir):
                        # 遍历envs目录下的所有环境
                        for env_name in os.listdir(envs_dir):
                            if not self._is_running:
                                return
                                
                            env_path = os.path.join(envs_dir, env_name)
                            if os.path.isdir(env_path):
                                # 检查该环境中的Python可执行文件
                                env_python = os.path.join(env_path, 'python.exe')
                                if os.path.isfile(env_python) and env_python not in python_paths:
                                    python_paths.append(env_python)
                                    self.log_message.emit(f"✓ 从conda环境找到Python: {env_python}\n", "success")
            
            # 检查是否在虚拟环境中
            if 'Scripts' in python_dir:
                # 获取虚拟环境根目录
                env_root = os.path.dirname(python_dir)
                if env_root and os.path.exists(env_root):
                    # 检查是否有其他虚拟环境在同一父目录下
                    parent_dir = os.path.dirname(env_root)
                    if os.path.exists(parent_dir):
                        for item in os.listdir(parent_dir):
                            if not self._is_running:
                                return
                                
                            item_path = os.path.join(parent_dir, item)
                            if os.path.isdir(item_path) and item != os.path.basename(env_root):
                                # 检查是否为虚拟环境
                                venv_python = os.path.join(item_path, 'Scripts', 'python.exe')
                                if os.path.isfile(venv_python) and venv_python not in python_paths:
                                    python_paths.append(venv_python)
                                    self.log_message.emit(f"✓ 从虚拟环境找到Python: {venv_python}\n", "success")
    
    def _detect_standalone_virtual_environments_from_env_managers(self, python_paths):
        """从环境管理器检测独立的虚拟环境（不依赖于已找到的Python）
        
        Args:
            python_paths (list): 已找到的Python路径列表
        """
        import glob
        
        self.log_message.emit("🔍 从环境管理器检测独立虚拟环境...\n", "info")
        
        # 获取环境管理器信息
        env_managers = self._get_env_managers()
        
        # 遍历环境管理器
        for manager in env_managers:
            if not self._is_running:
                return
                
            manager_path = manager['path']
            manager_type = manager['type']
            
            self.log_message.emit(f"🔍 检查{manager_type}环境管理器: {manager_path}\n", "info")
            
            if manager_type in ['conda', 'miniconda', 'anaconda', 'miniforge', 'mamba']:
                # 检查conda环境管理器的envs目录
                envs_dir = os.path.join(manager_path, 'envs')
                if os.path.exists(envs_dir):
                    # 遍历envs目录下的所有环境
                    for env_name in os.listdir(envs_dir):
                        if not self._is_running:
                            return
                            
                        env_path = os.path.join(envs_dir, env_name)
                        if os.path.isdir(env_path):
                            # 检查该环境中的Python可执行文件
                            env_python = os.path.join(env_path, 'python.exe')
                            if os.path.isfile(env_python) and env_python not in python_paths:
                                python_paths.append(env_python)
                                self.log_message.emit(f"✓ 从{manager_type}环境找到Python: {env_python}\n", "success")
                
                # 检查base环境
                base_python = os.path.join(manager_path, 'python.exe')
                if os.path.isfile(base_python) and base_python not in python_paths:
                    python_paths.append(base_python)
                    self.log_message.emit(f"✓ 从{manager_type} base环境找到Python: {base_python}\n", "success")
    
    def _get_env_managers(self):
        """获取已安装的Python环境管理器信息
        
        Returns:
            list: 包含环境管理器信息的列表，每个元素是包含type、path和source键的字典
        """
        import os
        
        env_managers = []  # 存储找到的环境管理器信息
        
        # 首先从环境变量获取Python环境管理器路径
        env_vars_to_check = [
            ('CONDA_PREFIX', 'conda'),      # Conda环境前缀（指向具体环境）
            ('CONDA_HOME', 'conda'),        # Conda主目录
            ('MINICONDA_HOME', 'miniconda'), # Miniconda主目录
            ('MINIFORGE_HOME', 'miniforge'), # Miniforge主目录
            ('MAMBA_HOME', 'mamba')         # Mamba主目录
        ]
        
        # 遍历环境变量，查找已安装的环境管理器
        for env_var, manager_type in env_vars_to_check:
            if env_var in os.environ:
                if env_var == 'CONDA_PREFIX':
                    # CONDA_PREFIX指向的是具体环境，需要获取基础目录
                    conda_prefix = os.environ[env_var]
                    # 检查是否在envs目录下，如果是，需要向上两级目录获取基础目录
                    if 'envs' in conda_prefix:
                        # 如果在envs目录下，说明是conda虚拟环境，需要向上两级获取conda安装根目录
                        base_path = os.path.dirname(os.path.dirname(conda_prefix))  # 从 envs/env_name 向上两级
                    else:
                        # 否则直接向上一级获取基础目录（可能是base环境）
                        base_path = os.path.dirname(conda_prefix)
                    
                    # 如果基础目录不包含miniforge3或anaconda3等，尝试向上查找
                    if not any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                        # 尝试在当前目录下查找这些目录
                        parent_dir = base_path
                        for _ in range(3):  # 最多向上查找3级目录
                            for name in ['miniforge3', 'anaconda3', 'miniconda3']:  # 常见的conda发行版目录名
                                test_path = os.path.join(parent_dir, name)  # 构建测试路径
                                if os.path.exists(test_path):  # 检查路径是否存在
                                    base_path = test_path  # 更新为基础路径
                                    break  # 找到后跳出内层循环
                            if any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                                break  # 找到有效的conda安装目录后跳出外层循环
                            parent_dir = os.path.dirname(parent_dir)  # 继续向上查找
                else:
                    # 对于其他环境变量，直接使用环境变量指向的路径作为基础路径
                    base_path = os.environ[env_var]  # 直接使用环境变量指向的路径
                
                # 将找到的环境管理器信息添加到列表
                env_managers.append({
                    'type': manager_type,
                    'path': base_path,
                    'source': f'环境变量 {env_var}'
                })
        
        # 如果没有从环境变量找到，搜索常见的安装路径
        if not env_managers:
            # 常见的Python环境管理器安装路径（覆盖多种安装位置）
            common_manager_paths = [
                # Miniconda3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniconda3'), 'miniconda'),
                # Miniconda3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniconda3'), 'miniconda'),
                # Miniconda3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniconda3'), 'miniconda'),
                
                # Anaconda3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Anaconda3'), 'anaconda'),
                # Anaconda3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Anaconda3'), 'anaconda'),
                # Anaconda3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Anaconda3'), 'anaconda'),
                
                # Miniforge3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniforge3'), 'miniforge'),
                # Miniforge3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniforge3'), 'miniforge'),
                # Miniforge3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniforge3'), 'miniforge'),
                
                # Mambaforge - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Mambaforge'), 'mamba'),
                # Mambaforge - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Mambaforge'), 'mamba'),
                # Mambaforge - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Mambaforge'), 'mamba'),
                
                # 用户主目录下的安装（手动安装到用户目录）
                (os.path.join(os.path.expanduser('~'), 'miniconda3'), 'miniconda'),
                (os.path.join(os.path.expanduser('~'), 'anaconda3'), 'anaconda'),
                (os.path.join(os.path.expanduser('~'), 'miniforge3'), 'miniforge'),
                (os.path.join(os.path.expanduser('~'), 'mambaforge'), 'mamba'),
                
                # 常见自定义安装路径（特定软件安装目录）
                ('F:\\itsoft\\miniforge3', 'miniforge'),
                ('C:\\itsoft\\miniforge3', 'miniforge'),
                ('D:\\itsoft\\miniforge3', 'miniforge'),
                ('E:\\itsoft\\miniforge3', 'miniforge')
            ]
                
            # 遍历所有常见安装路径，查找存在的环境管理器
            for manager_path, manager_type in common_manager_paths:
                if os.path.exists(manager_path):
                    env_managers.append({
                        'type': manager_type,
                        'path': manager_path,
                        'source': '常见安装路径'
                    })
        
        return env_managers
    
    def _get_virtual_env_root(self, python_path):
        """获取Python路径对应的虚拟环境根目录
        
        Args:
            python_path (str): Python可执行文件路径
            
        Returns:
            str: 虚拟环境根目录路径，如果不是虚拟环境则返回None
        """
        # 检查是否为虚拟环境中的Python
        # 虚拟环境的Python通常在Scripts目录下（Windows）
        if "Scripts" in python_path and python_path.endswith("python.exe"):
            # 获取Scripts目录的父目录
            scripts_dir = os.path.dirname(python_path)
            env_root = os.path.dirname(scripts_dir)
            # 验证是否为有效的虚拟环境
            if self._is_valid_virtual_environment(env_root):
                return env_root
        
        # 检查是否为conda环境
        # conda环境的Python通常在envs目录下
        if "envs" in python_path:
            # 向上查找直到找到envs目录
            parts = python_path.split(os.sep)
            for i in range(len(parts) - 1, -1, -1):
                if parts[i] == "envs":
                    # envs目录的父目录是conda根目录
                    conda_root = os.sep.join(parts[:i])
                    env_name = parts[i+1] if i+1 < len(parts) else ""
                    if env_name:
                        env_root = os.path.join(conda_root, "envs", env_name)
                        if self._is_valid_virtual_environment(env_root):
                            return env_root
        
        return None
    
    def _is_valid_virtual_environment(self, env_root):
        """验证是否为有效的虚拟环境
        
        Args:
            env_root (str): 虚拟环境根目录路径
            
        Returns:
            bool: 如果是有效的虚拟环境返回True，否则返回False
        """
        # 检查虚拟环境的关键文件和目录
        python_exe = os.path.join(env_root, 'Scripts', 'python.exe')
        pip_exe = os.path.join(env_root, 'Scripts', 'pip.exe')
        
        # 至少需要Python可执行文件
        if not os.path.isfile(python_exe):
            return False
        
        # 检查是否有虚拟环境标识文件
        pyvenv_cfg = os.path.join(env_root, 'pyvenv.cfg')
        if os.path.isfile(pyvenv_cfg):
            return True
        
        # 对于conda环境，检查conda-meta目录
        conda_meta = os.path.join(env_root, 'conda-meta')
        if os.path.isdir(conda_meta):
            return True
        
        # 检查是否有site-packages目录
        site_packages = os.path.join(env_root, 'Lib', 'site-packages')
        if os.path.isdir(site_packages):
            return True
        
        return False
    
    def _log_detection_performance(self, start_time, operation_name):
        """记录检测性能统计
        
        Args:
            start_time (float): 开始时间
            operation_name (str): 操作名称
        """
        import time
        
        end_time = time.time()
        duration = end_time - start_time
        
        self.log_message.emit(f"⏱️ {operation_name}耗时: {duration:.3f}秒\n", "info")
        
        # 更新检测计数
        self.detection_count += 1
        self.log_message.emit(f"📊 检测次数: {self.detection_count}\n", "info")
    
    def _update_detection_timestamp(self):
        """更新检测时间戳"""
        import time
        
        current_time = time.time()
        self.log_message.emit(f"🕐 检测完成时间: {current_time:.6f}\n", "info")


class CustomMessageBox(QDialog):
    """自定义消息框
    
    使用与主界面一致的NeumorphicButton样式的消息框，
    确保所有按钮样式统一。
    """
    def __init__(self, parent=None, title="", message="", icon_type="info"):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.setMinimumWidth(400)
        
        # 获取父窗口的DPI缩放比例
        if parent and hasattr(parent, 'dpi_scale'):
            self.dpi_scale = parent.dpi_scale
        else:
            screen = QApplication.primaryScreen()
            self.dpi_scale = screen.logicalDotsPerInch() / 96.0
        
        # 设置布局
        layout = QVBoxLayout()
        layout.setSpacing(self.get_scaled_size(20))
        layout.setContentsMargins(self.get_scaled_size(20), self.get_scaled_size(20), 
                                 self.get_scaled_size(20), self.get_scaled_size(20))
        
        # 添加图标和消息
        content_layout = QHBoxLayout()
        
        # 图标标签
        icon_label = QLabel()
        icon_label.setFixedSize(self.get_scaled_size(48), self.get_scaled_size(48))
        if icon_type == "info":
            icon_label.setStyleSheet("color: #2196F3; font-size: 32px;")
            icon_label.setText("ℹ")
        elif icon_type == "warning":
            icon_label.setStyleSheet("color: #FF9800; font-size: 32px;")
            icon_label.setText("⚠")
        elif icon_type == "error":
            icon_label.setStyleSheet("color: #F44336; font-size: 32px;")
            icon_label.setText("✗")
        elif icon_type == "success":
            icon_label.setStyleSheet("color: #4CAF50; font-size: 32px;")
            icon_label.setText("✓")
        
        content_layout.addWidget(icon_label)
        content_layout.addSpacing(self.get_scaled_size(15))
        
        # 消息文本
        message_label = QLabel(message)
        message_label.setWordWrap(True)
        message_label.setStyleSheet("font-size: 14px; color: #333333;")
        content_layout.addWidget(message_label, 1)
        
        layout.addLayout(content_layout)
        
        # 添加按钮
        self.button_layout = QHBoxLayout()
        self.button_layout.addStretch()
        
        # 确定按钮
        self.ok_button = QPushButton("确定", self)
        self.ok_button.setStyleSheet("""
            QPushButton {
                background-color: #BBDEFB;
                color: #000000;  /* 黑色文字 */
                font-family: "SimHei";  /* 黑体字体 */
                font-size: 16pt;
                border: 1px solid #90CAF9;
                border-radius: 5px;
                padding: 8px 20px;
                min-width: 80px;
            }
            QPushButton:hover {
                background-color: #90CAF9;
            }
            QPushButton:pressed {
                background-color: #64B5F6;
            }
        """)
        self.ok_button.setFixedHeight(self.get_scaled_size(28))
        self.ok_button.clicked.connect(self.accept)
        self.button_layout.addWidget(self.ok_button)
        
        layout.addLayout(self.button_layout)
        self.setLayout(layout)
        
        # 存储添加的按钮
        self.custom_buttons = {}
        
        # 初始化点击按钮
        self._clicked_button = None
        
        # 设置与主界面一致的主题色背景
        self.setStyleSheet("""
            QDialog {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 1, y2: 1, stop: 0 #E8F4FD, stop: 1 #F0F8FE);
                font-family: "Microsoft YaHei";
            }
        """)
    
    def get_scaled_size(self, base_size):
        """获取根据DPI缩放后的尺寸"""
        return int(base_size * self.dpi_scale)
    
    def addButton(self, text, role):
        """添加自定义按钮
        
        Args:
            text (str): 按钮文本
            role (QMessageBox.ButtonRole): 按钮角色
            
        Returns:
            QPushButton: 创建的按钮
        """
        button = QPushButton(text, self)
        button.setStyleSheet("""
            QPushButton {
                background-color: #BBDEFB;
                color: #000000;  /* 黑色文字 */
                font-family: "SimHei";  /* 黑体字体 */
                font-size: 16pt;
                border: 1px solid #90CAF9;
                border-radius: 5px;
                padding: 8px 20px;
                min-width: 80px;
            }
            QPushButton:hover {
                background-color: #90CAF9;
            }
            QPushButton:pressed {
                background-color: #64B5F6;
            }
        """)
        button.setFixedHeight(self.get_scaled_size(28))
        
        # 将按钮添加到布局中（在确定按钮之前）
        self.button_layout.insertWidget(self.button_layout.count() - 1, button)
        
        # 存储按钮引用
        self.custom_buttons[button] = role
        
        # 连接按钮点击信号
        def on_button_clicked():
            self._clicked_button = button
            self.accept()
        
        button.clicked.connect(on_button_clicked)
        
        return button
    
    def clickedButton(self):
        """获取点击的按钮
        
        Returns:
            QPushButton: 被点击的按钮，如果没有则返回None
        """
        return self._clicked_button
    
    def setText(self, text):
        """设置消息文本
        
        Args:
            text (str): 消息文本
        """
        # 查找消息标签并更新文本
        for i in range(self.layout().count()):
            item = self.layout().itemAt(i)
            if isinstance(item, QHBoxLayout):
                for j in range(item.count()):
                    widget_item = item.itemAt(j)
                    if isinstance(widget_item.widget(), QLabel):
                        label = widget_item.widget()
                        # 检查是否是消息标签（不是图标标签）
                        if label.text() not in ["ℹ", "⚠", "✗", "✓"]:
                            label.setText(text)
                            return
    
    def setIcon(self, icon):
        """设置图标
        
        Args:
            icon (QMessageBox.Icon): 图标类型
        """
        # 将QMessageBox.Icon转换为我们的icon_type
        icon_map = {
            QMessageBox.Information: "info",
            QMessageBox.Warning: "warning",
            QMessageBox.Critical: "error",
            QMessageBox.Question: "info"  # Question使用info图标
        }
        
        icon_type = icon_map.get(icon, "info")
        # 更新图标标签的样式
        for i in range(self.layout().count()):
            item = self.layout().itemAt(i)
            if isinstance(item, QHBoxLayout):
                for j in range(item.count()):
                    widget_item = item.itemAt(j)
                    if isinstance(widget_item.widget(), QLabel):
                        label = widget_item.widget()
                        if label.text() in ["ℹ", "⚠", "✗", "✓"]:
                            if icon_type == "info":
                                label.setStyleSheet("color: #2196F3; font-size: 32px;")
                                label.setText("ℹ")
                            elif icon_type == "warning":
                                label.setStyleSheet("color: #FF9800; font-size: 32px;")
                                label.setText("⚠")
                            elif icon_type == "error":
                                label.setStyleSheet("color: #F44336; font-size: 32px;")
                                label.setText("✗")
                            elif icon_type == "success":
                                label.setStyleSheet("color: #4CAF50; font-size: 32px;")
                                label.setText("✓")
                            break
    
    @staticmethod
    def information(parent, title, message):
        """显示信息消息框"""
        dialog = CustomMessageBox(parent, title, message, "info")
        dialog.exec_()
    
    @staticmethod
    def warning(parent, title, message):
        """显示警告消息框"""
        dialog = CustomMessageBox(parent, title, message, "warning")
        dialog.exec_()
    
    @staticmethod
    def critical(parent, title, message):
        """显示错误消息框"""
        dialog = CustomMessageBox(parent, title, message, "error")
        dialog.exec_()
    
    @staticmethod
    def success(parent, title, message):
        """显示成功消息框"""
        dialog = CustomMessageBox(parent, title, message, "success")
        dialog.exec_()

class NuitkaPackager(QMainWindow):
    # 常量定义 - 用于解析打包输出信息的正则表达式模式
    RESOURCE_PREFIX = "Resource: "  # 资源文件前缀
    MODULE_PREFIX = "Module: "      # 模块文件前缀
    PROGRESS_PATTERN = re.compile(r'Progress:\s*(\d+)%')        # 进度百分比模式
    C_LINKING_PATTERN = re.compile(r'Nuitka-Scons: Backend C linking with (\d+) files')  # C链接模式
    COMPILATION_PATTERN = re.compile(r'Nuitka-Scons:.*compiling')  # 编译模式
    LINKING_PATTERN = re.compile(r'Nuitka-Scons:.*linking')      # 链接模式
    
    def __init__(self):
        """初始化主窗口
        
        执行应用程序的初始化流程，包括窗口设置、变量初始化、
        UI组件创建、配置加载、环境检测等。
        """
        super().__init__()
        self.setWindowTitle("Nuitka EXE 打包工具 V7.0 星辰大海")  # 设置窗口标题
        
        # 实现分辨率自适应窗口设置
        self.setup_adaptive_window()
        
        # 设置窗口图标
        self.setWindowIcon(QIcon( r'F:\Python\ico-files\Pythontoexeico.ico'))
        
        # 使用临时目录存储配置文件
        self.temp_dir = tempfile.gettempdir()
        
        # 初始化配置变量
        self.mode_var = "onefile"          # 打包模式：单文件模式
        self.platform_var = "windows"      # 目标平台：固定为Windows
        self.opt_var = 0                    # Python优化级别：默认级别0
        self.jobs_var = min(4, os.cpu_count())  # 并行任务数：最多4个或CPU核心数
        self.upx_var = False                # UPX压缩：默认关闭
        self.upx_level = "best"            # UPX压缩级别：最佳压缩
        self.lto_var = "yes"                # LTO优化：默认yes
        self.compiler_var = "mingw"        # 编译器：Windows默认使用MinGW
        self.plugins = []                  # 插件列表：初始为空
        self.cleanup_cache = False           # 清理缓存：默认关闭
        self.console_var = "disable"       # 控制台设置：默认禁用
        self.multiprocessing_var = False     # multiprocessing插件：默认不启用

        # 初始化缓存相关变量
        self.python_cache = {}              # Python环境检测缓存
        self.cache_hit_count = 0            # 缓存命中次数
        self.total_detection_count = 0      # 总检测次数
        self.detection_times = []           # 检测耗时记录
        self.cache_dir = os.path.join(self.temp_dir, "nuitka_cache")  # 缓存目录

        # 配置文件路径
        self.config_path = os.path.join(self.temp_dir, "packager_config.json")
        
        # 日志文件管理（只在导出时创建）
        self.log_dir = os.path.join(os.getcwd(), "nuitka_logs")
        self.current_log_file = None
        self.current_python_path = None
        
        # 连续日志显示设置
        self.auto_scroll = True  # 默认自动滚动
        self.continuous_logging = True  # 启用连续日志记录
        self.user_action_logging = True  # 启用用户操作记录
        self.log_buffer = []  # 日志缓冲区
        self.max_log_buffer_size = 1000  # 最大缓冲区大小
        self.log_update_timer = QTimer(self)  # 日志更新定时器
        self.log_update_timer.timeout.connect(self.update_continuous_log)
        self.log_update_timer.start(500)  # 每500毫秒更新一次连续日志
        
        # 用户操作记录
        self.user_actions = []  # 用户操作列表
        self.max_user_actions = 100  # 最大用户操作记录数
        
        # 创建UI组件
        self.create_widgets()
        self.load_plugins()      # 加载插件列表
        self.load_config()       # 加载用户配置
        
        # 消息队列用于线程间通信
        self.message_queue = queue.Queue()
        self.running = False
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.check_queue)  # 连接定时器到消息检查函数
        self.timer.start(100)   # 每100毫秒检查一次消息队列
        
        # 创建线程管理器 - 统一管理所有后台线程
        self.thread_manager = ThreadManager()
        
        # 自动检测UPX工具
        self.detect_upx()
        
        # 添加启动日志和缓存信息
        self.log_message("🚀 程序启动完成，开始检测Python环境...\n", "info")
        self.log_message(f"📁 缓存目录位置: {self.cache_dir}\n", "info")
        
        # 检查并显示缓存文件状态
        cache_file = os.path.join(self.cache_dir, "python_paths_cache.pkl")
        timestamp_file = os.path.join(self.cache_dir, "last_detection_timestamp.txt")
        
        if os.path.exists(cache_file):
            self.log_message(f"✅ 发现缓存文件: {cache_file}\n", "success")
            try:
                import time
                cache_mtime = os.path.getmtime(cache_file)
                cache_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(cache_mtime))
                self.log_message(f"📅 缓存创建时间: {cache_time}\n", "info")
            except Exception:
                pass
        else:
            self.log_message(f"⚠ 未找到缓存文件，首次运行将创建缓存\n", "warning")
        
        # 使用线程管理器创建并启动Python环境检测线程
        thread = self.thread_manager.create_thread(
            PythonDetectionThread, 
            "python_detection",
            silent=True,  # 静默检测
            force=False   # 不强制重新检测
        )
        thread.detection_started.connect(lambda: self.log_message("🔍 开始后台检测Python环境...\n", "info"))
        thread.detection_progress.connect(lambda msg, progress: self.log_message(f"{msg}\n", "info"))
        thread.detection_completed.connect(self._on_detection_completed)
        thread.detection_failed.connect(lambda error: self.log_message(f"❌ 检测出错: {error}\n", "error"))
        self.detection_thread = thread
        self.thread_manager.start_thread("python_detection")
        
        # 添加完成日志
        self.log_message("✓ 初始化完成，环境检测在后台进行...\n", "success")
        
        # 应用现代化柔和主题
        self.setStyleSheet("""
            QMainWindow {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 1, y2: 1, stop: 0 #E8F4FD, stop: 1 #F0F8FE);  /* 更淡的天蓝色渐变背景 */
                font-family: "Microsoft YaHei";
            }
            QGroupBox {
                background-color: rgba(255, 255, 255, 200);  /* 半透明白色背景 */
                border: 1px solid #E0E0E0;
                border-radius: 15px;
                padding: 15px;
                margin-top: 1ex;
                font-weight: bold;
                color: #333333;  /* 深灰色文字 */
                font-family: "Microsoft YaHei";
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                subcontrol-position: top left;
                padding: 0 5px;
                left: 10px;
                color: #01579B;  /* 深蓝色标题 */
            }
            QLabel {
                color: #333333;  /* 深灰色文字 */
                font-family: "Microsoft YaHei";
            }
            QTextEdit {
                background-color: #FFFFFF;
                border: 1px solid #E0E0E0;
                border-radius: 10px;
                padding: 5px;
                color: #333333;  /* 深灰色文字 */
                font-family: "Consolas", "Microsoft YaHei";
            }
            QTextEdit QScrollBar:vertical {
                background: #E3F2FD;  /* 天蓝色背景 */
                width: 15px;
                border-radius: 4px;
                margin: 0px;
            }
            QTextEdit QScrollBar::handle:vertical {
                background: #87CEFA;  /* 天蓝色滑块 */
                border-radius: 4px;
                min-height: 20px;
            }
            QTextEdit QScrollBar::handle:vertical:hover {
                background: #4FC3F7;  /* 悬停时的天蓝色 */
            }
            QListWidget {
                background-color: #FFFFFF;
                border: 1px solid #E0E0E0;
                border-radius: 10px;
                padding: 5px;
                color: #333333;  /* 深灰色文字 */
                font-family: "Microsoft YaHei";
            }
            QLineEdit, QComboBox {
                background-color: #FFFFFF;
                border: 1px solid #E0E0E0;
                border-radius: 10px;
                padding: 5px;
                color: #333333;  /* 深灰色文字 */
                font-family: "Microsoft YaHei";
                height: 28px;
            }
            QProgressBar {
                background-color: #E0E0E0;
                border: 1px solid #BDBDBD;
                border-radius: 10px;
                text-align: center;
                height: 20px;
                font-weight: bold;
                color: #333333;  /* 深灰色文字 */
                font-family: "Microsoft YaHei";
            }
            QProgressBar::chunk {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 1, y2: 0, stop: 0 #4FC3F7, stop: 1 #039BE5);  /* 渐变蓝色进度条 */
                border-radius: 10px;
            }
            QTabWidget::pane {
                border: none;
                background: transparent;
                border-radius: 15px;
            }
            QTabBar::tab {
                background-color: #E3F2FD;
                color: #333333;  /* 深灰色文字 */
                font-size: 12pt;
                border: 1px solid #E0E0E0;
                padding: 8px 20px;
                margin-left: 5px;
                margin-right: 5px;
                border-top-left-radius: 10px;
                border-top-right-radius: 10px;
                font-family: "Microsoft YaHei";
            }
            QTabBar::tab:selected {
                background-color: #FFFFFF;
                border-bottom: none;
                font-weight: bold;
                color: #01579B;  /* 深蓝色文字 */
            }
            QRadioButton, QCheckBox {
                color: #333333;  /* 深灰色文字 */
                font-family: "Microsoft YaHei";
                spacing: 8px;
                font-size: 12pt;
            }
            QRadioButton::indicator, QCheckBox::indicator {
                width: 16px;
                height: 16px;
                border: 2px solid #B0BEC5;
      
                background-color: #FFFFFF;
            }
            QRadioButton::indicator:hover, QCheckBox::indicator:hover {
                border-color: #4FC3F7;
                background-color: #E3F2FD;
            }
            QRadioButton::indicator:checked, QCheckBox::indicator:checked {
                border-color: #4da27f;  /* 勾选后边框颜色 */
                background-color: #4da27f;  /* 勾选后背景颜色 */
                image: none;
            }
            QRadioButton::indicator:unchecked, QCheckBox::indicator:unchecked {
                border-color: #B0BEC5;
                background-color: #FFFFFF;
            }
            QRadioButton::indicator:pressed, QCheckBox::indicator:pressed {
                border-color: #01579B;
                background-color: #E1F5FE;
            }
            QRadioButton::indicator:disabled, QCheckBox::indicator:disabled {
                border-color: #E0E0E0;
                background-color: #F5F5F5;
            }
            QRadioButton::indicator:disabled:checked, QCheckBox::indicator:disabled:checked {
                border-color: #BDBDBD;
                background-color: #BDBDBD;
            }
            QSlider::groove:horizontal {
                height: 8px;
                background: #E0E0E0;
                border-radius: 4px;
            }
            QSlider::handle:horizontal {
                background: #FFFFFF;
                width: 18px;
                height: 18px;
                margin: -5px 0;
                border-radius: 9px;
                border: 2px solid #4FC3F7;
            }
            QSlider::sub-page:horizontal {
                background: qlineargradient(x1: 0, y1: 0, x2: 1, y2: 0, stop: 0 #4FC3F7, stop: 1 #039BE5);
                border-radius: 4px;
            }
            /* NeumorphicButton 样式已在类中定义，此处无需重复 */
            QMessageBox {
                background-color: #E3F2FD;  /* 天蓝色背景 */
                font-family: "SimHei";  /* 黑体字体 */
                color: #000000;  /* 黑色文字 */
                border: 1px solid #BBDEFB;
                border-radius: 10px;
            }
            QMessageBox QPushButton {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #B3E5FC, stop: 1 #81D4FA);
                color: #01579B;
                border: none;
                border-radius: 18px;
                padding: 8px 16px;
                font-weight: bold;
                font-size: 14px;
                min-width: 80px;
                min-height: 30px;
                outline: none;
            }
            QMessageBox QPushButton:hover {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #E1F5FE, stop: 1 #B3E5FC);
                margin-top: -1px;
                margin-bottom: 1px;
            }
            QMessageBox QPushButton:pressed {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #81D4FA, stop: 1 #4FC3F7);
                margin-top: 1px;
                margin-bottom: -1px;
            }
        """)
        
        # 延迟初始化滚动条位置，确保窗口完全显示后滚动条正确设置
        QTimer.singleShot(100, self._initialize_scroll_position)
    def _on_detection_completed(self, python_paths, from_cache=False):
        """处理Python环境检测完成后的操作
        
        Args:
            python_paths (list): 检测到的Python路径列表
            from_cache (bool): 是否从缓存读取的结果
        """
        self.log_message("✅ Python环境检测完成\n", "success")
        self.log_message(f"📋 检测到 {len(python_paths)} 个Python环境\n", "info")
        
        # 打印所有检测到的Python环境路径
        for i, path in enumerate(python_paths):
            self.log_message(f"🐍 Python环境 {i+1}: {path}\n", "info")
        
        # 只在真正执行了检测（而不是从缓存读取）时才保存缓存
        if not from_cache:
            try:
                cache_key = self._get_cache_key({})
                self._save_to_cache(cache_key, python_paths)
                self._update_detection_timestamp()
                self.log_message("✅ Python环境检测结果已保存到缓存\n", "success")
            except Exception as e:
                self.log_message(f"⚠ 保存缓存失败: {str(e)}\n", "warning")
        else:
            self.log_message("✅ 使用缓存的Python环境检测结果，无需重新保存\n", "success")
        
        # 使用检测到的Python路径填充选择框
        if python_paths:
            self.python_combo.clear()
            for path in python_paths:
                self.python_combo.addItem(path)
            # 自动选择第一个Python环境
            self.python_combo.setCurrentIndex(0)  # 使用setCurrentIndex更可靠
            self.log_message(f"✓ 已填充Python选择框，默认选择: {python_paths[0]}\n", "success")
        else:
            self.log_message("⚠ 未检测到任何Python环境，请手动选择或配置\n", "warning")
        
        # 检测Nuitka安装状态
        self.log_message("🔍 开始检测Nuitka安装状态...\n", "info")
        self.check_nuitka_installation()
        
        # 启动版本检测后台线程，避免阻塞UI
        python_cmd = python_paths[0] if python_paths else sys.executable
        
        # 检查是否已有版本检测线程在运行
        if hasattr(self, 'version_check_thread') and self.version_check_thread and self.version_check_thread.isRunning():
            self.log_message("⚠ 版本检测已在进行中...\n", "warning")
        else:
            thread = VersionCheckThread(python_cmd)
            thread.version_check_completed.connect(self._on_version_check_completed)
            thread.cache_hit.connect(self._on_cache_hit)
            self.version_check_thread = thread
            thread.start()  # 直接启动线程
        
        self.log_message("✅ 所有环境检测完成\n", "success")
    
    def _on_version_check_completed(self, python_version, nuitka_version):
        """处理版本检测完成后的操作"""
        # 清理线程引用
        if hasattr(self, 'version_check_thread'):
            self.version_check_thread = None
            
        try:
            # 获取Nuitka版本信息
            if nuitka_version:
                self.log_message(f"📦 Nuitka版本: {nuitka_version}\n", "info")
            else:
                self.log_message("📦 Nuitka版本: 未安装\n", "info")
            
            # 获取Python版本信息
            if python_version:
                self.log_message(f"🐍 Python版本: {python_version}\n", "info")
            else:
                self.log_message("🐍 Python版本: 未知\n", "info")
                
        except Exception as e:
            self.log_message(f"⚠ 读取版本信息失败: {str(e)}\n", "warning")
    
    def _on_cache_hit(self, python_version, nuitka_version):
        """处理缓存命中的情况"""
        # 清理线程引用
        if hasattr(self, 'version_check_thread'):
            self.version_check_thread = None
            
        try:
            self.log_message("✅ 使用缓存的版本信息\n", "success")
            
            # 获取Nuitka版本信息
            if nuitka_version:
                self.log_message(f"📦 Nuitka版本: {nuitka_version} (缓存)\n", "info")
            else:
                self.log_message("📦 Nuitka版本: 未安装 (缓存)\n", "info")
            
            # 获取Python版本信息
            if python_version:
                self.log_message(f"🐍 Python版本: {python_version} (缓存)\n", "info")
            else:
                self.log_message("🐍 Python版本: 未知 (缓存)\n", "info")
                
        except Exception as e:
            self.log_message(f"⚠ 读取缓存版本信息失败: {str(e)}\n", "warning")
    
    def _show_cached_versions(self):
        """从缓存中读取并展示Python版本和Nuitka版本信息"""
        try:
            # 获取当前选择的Python路径
            python_cmd = self.python_combo.currentText().strip() if self.python_combo.currentText().strip() else sys.executable
            
            # 生成缓存键
            cache_params = {
                'python_cmd': python_cmd,
                'timestamp': datetime.now().strftime('%Y-%m-%d')
            }
        
            # 获取Nuitka版本信息
            nuitka_version = self._get_nuitka_version(python_cmd)
            if nuitka_version:
                self.log_message(f"📦 Nuitka版本: {nuitka_version}\n", "info")
            else:
                self.log_message("📦 Nuitka版本: 未安装\n", "info")
            
            # 获取Python版本信息
            python_version = self._get_python_version(python_cmd)
            if python_version:
                self.log_message(f"🐍 Python版本: {python_version}\n", "info")
            else:
                self.log_message("🐍 Python版本: 未知\n", "info")
                
        except Exception as e:
            self.log_message(f"⚠ 读取版本信息失败: {str(e)}\n", "warning")
        
    def _get_python_version(self, python_cmd):
        """获取Python版本信息"""
        try:
            # 确保缓存字典存在
            if not hasattr(self, '_cached_python_versions'):
                self._cached_python_versions = {}
                
            # 首先检查是否有缓存的Python版本信息
            if python_cmd in self._cached_python_versions:
                return self._cached_python_versions[python_cmd]
                
            # Windows平台特殊处理，隐藏命令行窗口
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            # 执行python --version命令获取版本信息
            result = subprocess.run(
                [python_cmd, "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                startupinfo=startupinfo,
                shell=False
            )
            
            if result.returncode == 0:
                version = result.stdout.strip() or result.stderr.strip()
                if version.startswith("Python "):
                    version = version[7:]  # 去除"Python "前缀
                
                # 缓存结果到内存字典
                self._cached_python_versions[python_cmd] = version
                return version
            
        except Exception as e:
            self.log_message(f"⚠ 获取Python版本失败: {str(e)}\n", "warning")
        
        return None
    
    def _get_nuitka_version(self, python_cmd):
        """获取Nuitka版本信息"""
        try:
            # 确保缓存字典存在
            if not hasattr(self, '_cached_nuitka_versions'):
                self._cached_nuitka_versions = {}
                
            # 首先检查是否有缓存的Nuitka版本信息
            if python_cmd in self._cached_nuitka_versions:
                return self._cached_nuitka_versions[python_cmd]
                
            # Windows平台特殊处理，隐藏命令行窗口
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            # 执行python -m nuitka --version命令获取版本信息
            result = subprocess.run(
                [python_cmd, "-m", "nuitka", "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                startupinfo=startupinfo,
                shell=False
            )
            
            if result.returncode == 0:
                version = result.stdout.strip()
                # 清理版本信息，去除多余信息
                if "Nuitka" in version:
                    version = version.replace("Nuitka ", "").strip()
                if version.startswith("v") or version.startswith("V"):
                    version = version[1:].strip()
                
                # 缓存结果到内存字典
                self._cached_nuitka_versions[python_cmd] = version
                return version
            
        except Exception as e:
            self.log_message(f"⚠ 获取Nuitka版本失败: {str(e)}\n", "warning")
        
        return None
        
    def setup_adaptive_window(self):
        """设置分辨率自适应窗口
        
        根据屏幕尺寸和DPI缩放比例自动调整窗口大小和位置，
        实现跨不同分辨率和DPI设置的自适应显示效果。
        窗口大小设置为屏幕的85%，最大不超过1100x1500像素，
        最小尺寸为800x600像素，并确保窗口居中显示。
        """
        # 获取主屏幕信息
        screen = QApplication.primaryScreen()
        screen_geometry = screen.geometry()
        screen_width = screen_geometry.width()
        screen_height = screen_geometry.height()
        
        # 获取屏幕DPI缩放比例（96 DPI为标准值）
        dpi_scale = screen.logicalDotsPerInch() / 96.0
        
        # 计算自适应窗口大小（屏幕的80%，最大不超过1200x900）
        window_height = min(int(screen_height * 0.80), 900)  # 从1500改为900
        window_width = min(int(screen_width * 0.80), 1200)
        
        # 根据DPI缩放调整窗口大小
        window_width = int(window_width * dpi_scale)
        window_height = int(window_height * dpi_scale)
        
        # 确保窗口不小于最小尺寸
        min_width = max(900, int(800 * dpi_scale))
        min_height = max(900, int(500 * dpi_scale))  # 减小最小高度，从1100改为700，基础高度从600改为500
        window_width = max(window_width, min_width)
        window_height = max(window_height, min_height)
        
        # 计算窗口居中位置
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2
        
        # 设置窗口几何位置和大小
        self.setGeometry(x, y, window_width, window_height)
        
        # 设置最小窗口尺寸
        self.setMinimumSize(min_width, min_height)
        
        # 启用DPI感知和触摸事件支持
        self.setAttribute(Qt.WA_AcceptTouchEvents)
        
        # 存储DPI缩放比例供后续使用
        self.dpi_scale = dpi_scale
        
        # 连接窗口大小变化事件处理器
        self.resizeEvent = self.on_resize_event
        
    def on_resize_event(self, event):
        """处理窗口大小变化事件
        
        当用户调整窗口大小时触发此事件，
        目前仅调用父类的事件处理，可在此处添加
        窗口大小变化时的自定义响应逻辑，如重新布局控件、
        调整字体大小等。
        
        Args:
            event: 窗口大小变化事件对象，包含新的窗口尺寸信息
        """
        # 调用父类的resizeEvent以保持默认行为
        super().resizeEvent(event)

        
    def get_scaled_size(self, base_size):
        """获取根据DPI缩放后的尺寸
        
        根据当前屏幕的DPI缩放比例对基础尺寸进行缩放计算，
        确保UI元素在不同DPI设置下保持合适的视觉比例。
        
        Args:
            base_size (int): 基础尺寸值（像素）
            
        Returns:
            int: 根据DPI缩放后的尺寸值（像素）
        """
        return int(base_size * self.dpi_scale)
        
    def apply_combo_style(self, combo):
        """为QComboBox应用统一的样式，使用原来Python选择下拉菜单的原始样式"""
        combo.setEditable(False)
        combo.setPlaceholderText("选择选项")
        combo.setStyleSheet("""
            QComboBox {
                padding: 5px;
                border: 1px solid #CCCCCC;
                border-radius: 4px;
                background: white;
                font-family: "Microsoft YaHei";
                font-weight: bold;
                color: #000000;  /* 黑色文字 */
            }
            QComboBox:hover {
                background-color: #E3F2FD;  /* 天蓝色背景 */
            }
            QComboBox QAbstractItemView {
                background-color: #F5F9FC;  /* 柔和的浅蓝色背景，与整体主题协调 */
                border: 1px solid #E0E0E0;
                border-radius: 4px;
                selection-background-color: #E3F2FD;  /* 选中项背景色 */
                selection-color: #01579B;  /* 选中项文字颜色 */
                font-family: "Microsoft YaHei";  /* 黑体 */
                font-weight: bold;  /* 加粗 */
                color: #000000;  /* 黑色文字 */
            }
            QComboBox QAbstractItemView::item:hover {
                background-color: #E3F2FD;  /* 鼠标悬停时天蓝色高亮 */
            }
            QComboBox::drop-down {
                subcontrol-origin: padding;
                subcontrol-position: top right;
                width: 20px;  /* 增加下拉箭头宽度 */
                border-left-width: 1px;
                border-left-color: #CCCCCC;
                border-left-style: solid;
                border-top-right-radius: 4px;
                border-bottom-right-radius: 4px;
                background-color: #F5F9FC;  /* 下拉箭头区域背景色 */
            }
            QComboBox::down-arrow {
                image: url("F:/Python/ico-files/down_arrow.png");
                width: 16px;
                height: 16px;
            }
            QComboBox::down-arrow:on {
                top: 1px;
                left: 1px;
            }
        """)
        
    def get_scaled_font(self, base_point_size):
        """获取根据DPI缩放后的字体
        
        根据当前屏幕的DPI缩放比例创建缩放后的字体对象，
        确保文字在不同DPI设置下保持良好的可读性和一致性。
        
        Args:
            base_point_size (int): 基础字体大小（磅值）
            
        Returns:
            QFont: 根据DPI缩放后的字体对象
        """
        font = QFont("Microsoft YaHei")
        font.setPointSize(int(base_point_size * self.dpi_scale))
        return font
        
    def create_widgets(self):
        """创建所有UI组件和布局
        
        初始化应用程序的用户界面，包括主窗口布局、标题栏、
        标签页、各种输入控件和按钮等。所有UI元素都会根据
        当前DPI设置进行自适应缩放。
        """
        # 主布局容器和布局管理器
        main_widget = QWidget()
        main_layout = QVBoxLayout(main_widget)
        # 减少主布局的边距，使界面更紧凑
        main_layout.setContentsMargins(self.get_scaled_size(3), self.get_scaled_size(3), 
                                     self.get_scaled_size(3), self.get_scaled_size(3))
        main_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        self.setCentralWidget(main_widget)
        
        # 简化标题栏布局
        title_layout = QHBoxLayout()
        title_layout.setContentsMargins(0, 0, 0, 0)
        
        # 应用程序标题标签
        title_label = QLabel("Nuitka EXE 打包工具")
        title_label.setFont(self.get_scaled_font(14))  # 稍微减小字体
        title_label.setStyleSheet("color: #1565C0; font-weight: bold;")  # 使用更鲜明的蓝色并加粗
        title_layout.addWidget(title_label)
        
        # 添加弹性空间
        title_layout.addStretch(1)
        
        # 帮助按钮 - 简化样式
        help_btn = NeumorphicButton("帮助")
        help_btn.setFixedHeight(self.get_scaled_size(28))   # 减小按钮高度
        help_btn.setFixedWidth(self.get_scaled_size(80))    # 减小按钮宽度
        help_btn.clicked.connect(self.show_help)            
        title_layout.addWidget(help_btn)
        main_layout.addLayout(title_layout)
        
        # 简化分隔线
        line = QFrame()
        line.setFrameShape(QFrame.HLine)
        line.setFrameShadow(QFrame.Sunken)
        line.setStyleSheet(f"background-color: #BBDEFB; height: {self.get_scaled_size(1)}px;")  # 更细更淡的线
        main_layout.addWidget(line)
        
        # 标签页 - 减小标签高度
        tab_widget = QTabWidget()
        tab_widget.setDocumentMode(True)
        tab_widget.setStyleSheet(f"""
            QTabBar::tab {{ 
                height: {self.get_scaled_size(18)}px; 
                padding: {self.get_scaled_size(5)}px {self.get_scaled_size(10)}px;
                margin-right: {self.get_scaled_size(2)}px;
                background-color: #E3F2FD;
                border: 1px solid #BBDEFB;
                border-bottom: none;
                border-top-left-radius: {self.get_scaled_size(4)}px;
                border-top-right-radius: {self.get_scaled_size(4)}px;
            }}
            QTabBar::tab:selected {{
                background-color: #FFFFFF;
                border-color: #90CAF9;
            }}
            QTabWidget::pane {{
                border: 1px solid #90CAF9;
                background-color: #FFFFFF;
                border-radius: {self.get_scaled_size(4)}px;
            }}
        """)
        main_layout.addWidget(tab_widget, 2)
        
        # 基础配置标签页
        basic_tab = QWidget()
        self.create_basic_tab(basic_tab)
        tab_widget.addTab(basic_tab, "基础配置")
        
        
        # 依赖管理标签页
        deps_tab = QWidget()
        self.create_deps_tab(deps_tab)
        tab_widget.addTab(deps_tab, "依赖管理")
        
        # 高级设置标签页
        advanced_tab = QWidget()
        self.create_advanced_tab(advanced_tab)
        tab_widget.addTab(advanced_tab, "高级设置")
        
        # 日志区域
        log_group = QGroupBox("日志输出")
        log_layout = QVBoxLayout()
        log_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), 
                                     self.get_scaled_size(5), self.get_scaled_size(5))
        log_layout.setSpacing(self.get_scaled_size(5))
        log_group.setLayout(log_layout)
        
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setFont(self.get_scaled_font(12))
        self.log_text.setMinimumHeight(self.get_scaled_size(350))  # 设置最小高度
        
        # 添加滚动控制功能
        self.auto_scroll = True  # 默认自动滚动
        self.log_text.verticalScrollBar().valueChanged.connect(self.on_scroll_changed)
        self.log_text.mouseDoubleClickEvent = self.on_log_double_click
        
        log_layout.addWidget(self.log_text)
        main_layout.addWidget(log_group, 3) # 日志区域占2份空间
        
        
        # 进度条和按钮区域
        button_frame = QWidget()
        button_layout = QHBoxLayout(button_frame)
        button_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), 
                                       self.get_scaled_size(5), self.get_scaled_size(5))
        button_layout.setSpacing(self.get_scaled_size(5))
        
        self.progress = QProgressBar()
        self.progress.setMinimum(0)
        self.progress.setMaximum(100)
        self.progress.setAlignment(Qt.AlignCenter)
        self.progress.setFormat("%p% - 准备就绪")  # 显示百分比和状态文本
        self.progress.setFixedHeight(self.get_scaled_size(25))
        button_layout.addWidget(self.progress, 3)
        
        self.start_button = NeumorphicButton("开始打包")
        self.start_button.setFixedHeight(self.get_scaled_size(35))
        self.start_button.setFixedWidth(self.get_scaled_size(110))
        self.start_button.clicked.connect(self.start_packaging)
        button_layout.addWidget(self.start_button)
        
        self.stop_button = NeumorphicButton("停止打包")
        self.stop_button.setFixedHeight(self.get_scaled_size(35))
        self.stop_button.setFixedWidth(self.get_scaled_size(110))
        self.stop_button.clicked.connect(self.stop_packaging)
        self.stop_button.setEnabled(False)
        self.stop_button.setStyleSheet("""
            NeumorphicButton {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #B3E5FC, stop: 1 #81D4FA);
                color: #01579B;
                border: none;
                border-radius: 18px;
                padding: 8px 16px;
                font-weight: bold;
                font-size: 14px;
                min-width: 80px;
                outline: none;
            }
            NeumorphicButton:hover {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #E1F5FE, stop: 1 #B3E5FC);
                margin-top: -1px;
                margin-bottom: 1px;
            }
            NeumorphicButton:pressed {
                background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, 
                    stop: 0 #81D4FA, stop: 1 #4FC3F7);
                margin-top: 1px;
                margin-bottom: -1px;
            }
        """)
        button_layout.addWidget(self.stop_button)
        
        self.clear_log_button = NeumorphicButton("清除日志")
        self.clear_log_button.setFixedHeight(self.get_scaled_size(35))
        self.clear_log_button.setFixedWidth(self.get_scaled_size(110))
        self.clear_log_button.clicked.connect(self.clear_logs)
        button_layout.addWidget(self.clear_log_button)

        self.export_button = NeumorphicButton("导出日志")
        self.export_button.setFixedHeight(self.get_scaled_size(35))
        self.export_button.setFixedWidth(self.get_scaled_size(110))
        self.export_button.clicked.connect(self.export_logs)
        button_layout.addWidget(self.export_button)
        
        main_layout.addWidget(button_frame)
    
    def create_basic_tab(self, tab):
        """创建基础配置标签页
        
        创建包含Python环境设置、项目配置、打包模式、
        控制台设置和图标设置等基础打包选项的UI界面。
        
        Args:
            tab: 要添加UI组件的标签页容器
        """
        # 设置标签页主布局 - 减少间距和边距
        layout = QVBoxLayout(tab)
        layout.setSpacing(self.get_scaled_size(3))        # 减少GroupBox之间的垂直间距
        layout.setContentsMargins(self.get_scaled_size(3), self.get_scaled_size(3), 
                                 self.get_scaled_size(3), self.get_scaled_size(3))  # 减少边距
        
        # === Python环境设置组 - 简化样式 ===
        env_group = QGroupBox("Python环境")
        env_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        env_layout = QGridLayout()  # 使用网格布局
        env_layout.setSpacing(self.get_scaled_size(3))   # 减少网格间距
        env_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                     self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距

        # Python解释器路径选择 - 减小控件尺寸
        python_label = QLabel("Python解释器:")
        python_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        python_label.setMinimumWidth(self.get_scaled_size(80))  # 减小标签宽度
        python_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        
        self.python_combo = QComboBox()
        self.apply_combo_style(self.python_combo)
        self.python_combo.setPlaceholderText("选择或输入Python解释器路径 (可选)")
        self.python_combo.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        self.python_combo.currentTextChanged.connect(self.on_python_combo_changed)
        
        # 按钮布局 - 减少按钮数量和尺寸
        python_btn_layout = QHBoxLayout()
        python_btn_layout.setSpacing(self.get_scaled_size(3))  # 减少按钮间距
        python_btn_layout.setContentsMargins(0, 0, 0, 0)  # 无内边距
        
        # 浏览Python解释器按钮
        python_btn = NeumorphicButton("浏览")
        python_btn.clicked.connect(self.browse_python)
        python_btn.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        python_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        python_btn_layout.addWidget(python_btn)
        
        # 自动检测Python环境按钮
        auto_detect_btn = NeumorphicButton("检测")
        auto_detect_btn.clicked.connect(lambda: self.start_python_detection(silent=False, force=True))
        auto_detect_btn.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        auto_detect_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        python_btn_layout.addWidget(auto_detect_btn)
        
        # 将组件添加到网格布局
        env_layout.addWidget(python_label, 0, 0)
        env_layout.addWidget(self.python_combo, 0, 1)
        env_layout.addLayout(python_btn_layout, 0, 2)
        
        # 设置列的拉伸策略
        env_layout.setColumnStretch(0, 0)  # 标签列不拉伸
        env_layout.setColumnStretch(1, 1)  # 下拉框列拉伸
        env_layout.setColumnStretch(2, 0)  # 按钮列不拉伸
        
        env_group.setLayout(env_layout)
        layout.addWidget(env_group)
        
        # 项目设置组和运行管理组（水平布局）
        project_run_layout = QHBoxLayout()
        project_run_layout.setSpacing(20)  # 增加水平间距
        
        # 项目设置组 - 简化样式和布局
        project_group = QGroupBox("项目设置")
        project_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        project_layout = QVBoxLayout(project_group)
        project_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        project_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                         self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距
        
        # 脚本路径选择 - 减小控件尺寸
        script_layout = QHBoxLayout()
        script_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        script_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        script_label = QLabel("脚本路径:")
        script_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        script_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        script_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        script_layout.addWidget(script_label)
        self.script_entry = QLineEdit()  # 脚本路径输入框
        self.script_entry.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        self.script_entry.textChanged.connect(self.on_script_path_changed)  # 连接文本变化信号
        script_layout.addWidget(self.script_entry, 1)  # 占据1份空间
        script_browse = NeumorphicButton("浏览")
        script_browse.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        script_browse.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        script_browse.clicked.connect(self.browse_script)  # 浏览脚本文件
        script_layout.addWidget(script_browse)
        
        scan_btn = NeumorphicButton("扫描依赖")
        scan_btn.setFixedWidth(self.get_scaled_size(80))  # 减小按钮宽度
        scan_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        scan_btn.clicked.connect(self.scan_dependencies)  # 扫描项目依赖
        script_layout.addWidget(scan_btn)
        
        project_layout.addLayout(script_layout)
        
        # 输出目录设置 - 减小控件尺寸
        output_layout = QHBoxLayout()
        output_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        output_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        output_label = QLabel("输出目录:")
        output_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        output_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        output_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        output_layout.addWidget(output_label)
        self.output_entry = QLineEdit()  # 输出目录输入框
        self.output_entry.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        output_layout.addWidget(self.output_entry, 1)  # 占据1份空间
        
        output_browse = NeumorphicButton("浏览")
        output_browse.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        output_browse.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        output_browse.clicked.connect(self.browse_output)  # 浏览输出目录
        output_layout.addWidget(output_browse)
        
        # 添加打开输出目录按钮
        output_open = NeumorphicButton("打开路径")
        output_open.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        output_open.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        output_open.clicked.connect(self.open_output_directory)  # 打开输出目录
        output_layout.addWidget(output_open)
        
        project_layout.addLayout(output_layout)
        
        # 应用程序图标设置 - 减小控件尺寸
        icon_layout = QHBoxLayout()
        icon_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        icon_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        icon_label = QLabel("应用图标:")
        icon_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        icon_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        icon_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        icon_layout.addWidget(icon_label)
        self.icon_entry = QLineEdit()  # 图标路径输入框
        self.icon_entry.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        icon_layout.addWidget(self.icon_entry, 1)  # 占据1份空间
        self.icon_entry.setPlaceholderText("图标文件路径")  # 设置占位符
        
        icon_browse = NeumorphicButton("浏览")
        icon_browse.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        icon_browse.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        icon_browse.clicked.connect(self.browse_icon)  # 浏览图标文件
        icon_layout.addWidget(icon_browse)
        
        # 添加转换为ICO格式按钮
        icon_convert = NeumorphicButton("转换图标")
        icon_convert.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        icon_convert.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        icon_convert.clicked.connect(self.convert_to_ico)  # 转换为ICO格式
        icon_layout.addWidget(icon_convert)
        
        project_layout.addLayout(icon_layout)
        
        # 可执行文件名设置 - 减小控件尺寸
        name_layout = QHBoxLayout()
        name_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        name_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        name_label = QLabel("EXE名称:")
        name_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        name_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        name_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        name_layout.addWidget(name_label)
        self.name_entry = QLineEdit()  # 文件名输入框
        self.name_entry.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        name_layout.addWidget(self.name_entry, 1)  # 占据1份空间
        project_layout.addLayout(name_layout)
        
        project_run_layout.addWidget(project_group, 1)  # 拉伸因子为1
        
        # 运行管理组 - 简化样式和布局
        run_group = QGroupBox("运行管理")
        run_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        run_layout = QVBoxLayout(run_group)
        run_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        run_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                     self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距
        
        # 运行Python文件设置 - 减小控件尺寸
        run_py_layout = QHBoxLayout()
        run_py_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        run_py_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        run_py_label = QLabel("运行Py文件:")
        run_py_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        run_py_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        run_py_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        run_py_layout.addWidget(run_py_label)
        self.run_py_entry = QLineEdit()  # Python文件路径输入框
        self.run_py_entry.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        run_py_layout.addWidget(self.run_py_entry, 1)  # 占据1份空间
        self.run_py_entry.setPlaceholderText("将使用脚本路径中的Python文件")  # 设置占位符
        
        run_py_btn = NeumorphicButton("运行")
        run_py_btn.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        run_py_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        run_py_btn.clicked.connect(self.run_python_file)  # 运行Python文件
        run_py_layout.addWidget(run_py_btn)
        
        run_layout.addLayout(run_py_layout)
        
        # 包管理命令设置 - 减小控件尺寸
        pkg_cmd_layout = QHBoxLayout()
        pkg_cmd_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        pkg_cmd_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        pkg_cmd_label = QLabel("包管理:")
        pkg_cmd_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        pkg_cmd_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        pkg_cmd_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        pkg_cmd_layout.addWidget(pkg_cmd_label)
        self.pkg_manager_combo = QComboBox()  # 包管理器选择下拉框
        self.pkg_manager_combo.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        self.pkg_manager_combo.addItems(["pip", "conda", "mamba"])
        self.apply_combo_style(self.pkg_manager_combo)  # 应用统一下拉框样式
        pkg_cmd_layout.addWidget(self.pkg_manager_combo, 1)  # 占据1份空间
        
        self.pkg_action_combo = QComboBox()  # 操作类型选择下拉框
        self.pkg_action_combo.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        self.pkg_action_combo.addItems(["install", "uninstall"])
        self.apply_combo_style(self.pkg_action_combo)  # 应用统一下拉框样式
        pkg_cmd_layout.addWidget(self.pkg_action_combo, 1)  # 占据1份空间
        
        self.pkg_cmd_entry = QLineEdit()  # 包名输入框
        self.pkg_cmd_entry.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        pkg_cmd_layout.addWidget(self.pkg_cmd_entry, 2)  # 占据2份空间
        self.pkg_cmd_entry.setPlaceholderText("输入包名")  # 设置占位符
        
        pkg_cmd_btn = NeumorphicButton("执行")
        pkg_cmd_btn.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        pkg_cmd_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        pkg_cmd_btn.clicked.connect(self.run_pkg_management)  # 执行包管理命令
        pkg_cmd_layout.addWidget(pkg_cmd_btn)
        
        run_layout.addLayout(pkg_cmd_layout)
        
        # Python环境包查询设置 - 减小控件尺寸
        pkg_query_layout = QHBoxLayout()
        pkg_query_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        pkg_query_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        pkg_query_label = QLabel("环境查询:")
        pkg_query_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        pkg_query_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        pkg_query_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        pkg_query_layout.addWidget(pkg_query_label)

        # 查询结果说明 - 简化文本
        packages_tip = QLabel("查询已安装包")
        packages_tip.setStyleSheet("color: #666666; font-size: 9pt;")
        pkg_query_layout.addWidget(packages_tip, 1)  # 添加拉伸因子，占据剩余空间
        
        # 查询环境包按钮
        query_packages_btn = NeumorphicButton("查询")
        query_packages_btn.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        query_packages_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        query_packages_btn.clicked.connect(self.query_python_packages)
        pkg_query_layout.addWidget(query_packages_btn)
        
        run_layout.addLayout(pkg_query_layout)
        
        # 手动清理缓存设置 - 简化布局
        manual_cleanup_layout = QHBoxLayout()
        manual_cleanup_layout.setSpacing(self.get_scaled_size(3))  # 减小间距
        manual_cleanup_layout.setContentsMargins(0, 0, 0, 0)  # 移除边距
        cleanup_label = QLabel("缓存清理:")
        cleanup_label.setStyleSheet("font-weight: bold; font-size: 10pt;")
        cleanup_label.setMinimumWidth(self.get_scaled_size(60))  # 减小标签最小宽度
        cleanup_label.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        manual_cleanup_layout.addWidget(cleanup_label)
        
        # 清理状态说明 - 简化文本
        cleanup_tip = QLabel("清理临时文件和缓存")
        cleanup_tip.setStyleSheet("color: #666666; font-size: 9pt;")
        manual_cleanup_layout.addWidget(cleanup_tip)
        
        # 添加拉伸因子，占据剩余空间
        manual_cleanup_layout.addStretch(1)

        # 清理临时文件复选框
        self.cleanup_cb = QCheckBox("自动清理")
        self.cleanup_cb.setChecked(self.cleanup_cache)  # 默认开启清理
        self.cleanup_cb.toggled.connect(lambda state: setattr(self, 'cleanup_cache', state))  # 更新状态
        self.cleanup_cb.setFixedHeight(self.get_scaled_size(32))  # 减小高度
        manual_cleanup_layout.addWidget(self.cleanup_cb)
        
        # 手动清理缓存按钮
        manual_cleanup_btn = NeumorphicButton("清理")
        manual_cleanup_btn.setFixedWidth(self.get_scaled_size(70))  # 减小按钮宽度
        manual_cleanup_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        manual_cleanup_btn.clicked.connect(self.manual_cleanup_cache)
        manual_cleanup_layout.addWidget(manual_cleanup_btn)
        
        run_layout.addLayout(manual_cleanup_layout)
        
        project_run_layout.addWidget(run_group, 1)  # 拉伸因子为1
        
        layout.addLayout(project_run_layout)
        
        # 打包模式与控制台设置（水平布局） - 简化样式和布局
        mode_console_layout = QHBoxLayout()
        mode_console_layout.setSpacing(self.get_scaled_size(5))  # 减小水平间距
        
        # 打包模式选择组 - 添加样式
        mode_group = QGroupBox("打包模式")
        mode_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        mode_layout = QVBoxLayout(mode_group)
        mode_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        mode_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                     self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距
        
        # 单文件模式选项 - 减小高度
        self.onefile_rb = QRadioButton("单文件模式")
        self.onefile_rb.setChecked(True)  # 默认选中单文件模式
        self.onefile_rb.setFixedHeight(self.get_scaled_size(28))  # 减小高度
        self.onefile_rb.toggled.connect(lambda: self.update_mode("onefile"))  # 切换模式
        mode_layout.addWidget(self.onefile_rb)
        
        # 目录模式选项 - 减小高度
        self.standalone_rb = QRadioButton("目录模式")
        self.standalone_rb.setFixedHeight(self.get_scaled_size(28))  # 减小高度
        self.standalone_rb.toggled.connect(lambda: self.update_mode("standalone"))  # 切换模式
        mode_layout.addWidget(self.standalone_rb)
        
        mode_console_layout.addWidget(mode_group, 1)  # 平分区域
        
        # 控制台选项组（仅Windows） - 添加样式
        console_group = QGroupBox("控制台设置")
        console_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        console_layout = QVBoxLayout(console_group)
        console_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        console_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                        self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距
        
        # 显示控制台选项 - 减小高度
        self.console_enable_rb = QRadioButton("显示控制台")
        self.console_enable_rb.setFixedHeight(self.get_scaled_size(28))  # 减小高度
        self.console_enable_rb.toggled.connect(lambda: self.update_console("enable"))  # 启用控制台
        console_layout.addWidget(self.console_enable_rb)
        
        # 禁用控制台选项 - 减小高度
        self.console_disable_rb = QRadioButton("禁用控制台")
        self.console_disable_rb.setChecked(True)  # 默认禁用控制台
        self.console_disable_rb.setFixedHeight(self.get_scaled_size(28))  # 减小高度
        self.console_disable_rb.toggled.connect(lambda: self.update_console("disable"))  # 禁用控制台
        console_layout.addWidget(self.console_disable_rb)
        
        mode_console_layout.addWidget(console_group, 1)  # 平分区域
        
        layout.addLayout(mode_console_layout)
        

        
        # 图标设置组已移到项目设置组的水平布局中
        

    
    def create_deps_tab(self, tab):
        """创建依赖管理标签页, 包含常用插件列表和自定义依赖管理功能
        
        Args:
            tab: QTabWidget的标签页容器, 用于放置依赖管理相关的UI组件
        """
        # 设置标签页的主布局，使用垂直布局管理器
        layout = QVBoxLayout(tab)
        layout.setSpacing(self.get_scaled_size(5))  # 减少GroupBox之间的垂直间距
        layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), 
                                 self.get_scaled_size(5), self.get_scaled_size(5))  # 统一设置边距
        
        # =========== 常用插件组 ===========
        plugin_group = QGroupBox("常用插件")
        plugin_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        plugin_layout = QVBoxLayout(plugin_group)
        plugin_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        plugin_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                        self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距
        
        # 创建插件列表控件，支持多选模式
        self.plugin_list = QListWidget()
        self.plugin_list.setSelectionMode(QListWidget.MultiSelection)
        # 设置插件列表样式，优化性能减少动画卡顿
        self.plugin_list.setStyleSheet(f"""
            QListWidget {{
                background-color: #FFFFFF;
                border: 1px solid #E0E0E0;
                font-size: {self.get_scaled_size(12)}px;
                outline: none;
            }}
            QListWidget::item:selected {{
                background-color: #B3E5FC;
                color: #01579B;
                border: none;
            }}
            QListWidget::item:hover {{
                background-color: #F0F8FF;
                border: none;
            }}
            QListWidget::item:focus {{
                outline: none;
                border: none;
            }}
        """)
        plugin_layout.addWidget(self.plugin_list)
        
        # 添加使用提示信息 - 简化文本
        upx_tip = QLabel("提示: UPX 压缩需要将 upx.exe 添加到系统 PATH")
        upx_tip.setStyleSheet("color: #666666; font-size: 9pt;")
        plugin_layout.addWidget(upx_tip)
        
        layout.addWidget(plugin_group)
        
        # =========== 自定义依赖组 ===========
        custom_group = QGroupBox("自定义依赖")
        custom_group.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                font-size: 11pt;
                color: #1565C0;
                border: 1px solid #BBDEFB;
                border-radius: {self.get_scaled_size(4)}px;
                margin-top: {self.get_scaled_size(6)}px;
                padding-top: {self.get_scaled_size(6)}px;
                background-color: #F5F9FF;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: {self.get_scaled_size(6)}px;
                padding: 0 {self.get_scaled_size(3)}px 0 {self.get_scaled_size(3)}px;
            }}
        """)
        custom_layout = QVBoxLayout(custom_group)
        custom_layout.setSpacing(self.get_scaled_size(3))  # 减少组件间距
        custom_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(10), 
                                        self.get_scaled_size(5), self.get_scaled_size(5))  # 减少内边距
        
        # 创建自定义依赖列表控件（支持多选）
        self.deps_list = QListWidget()
        self.deps_list.setSelectionMode(QListWidget.ExtendedSelection)  # 支持Ctrl+点击和Shift+点击多选
        # 设置依赖列表样式，优化性能减少动画卡顿
        self.deps_list.setStyleSheet(f"""
            QListWidget {{
                background-color: #FFFFFF;
                border: 1px solid #E0E0E0;
                font-size: {self.get_scaled_size(12)}px;
                outline: none;
            }}
            QListWidget::item:selected {{
                background-color: #B3E5FC;
                color: #01579B;
                border: none;
            }}
            QListWidget::item:hover {{
                background-color: #F0F8FF;
                border: none;
            }}
            QListWidget::item:focus {{
                outline: none;
                border: none;
            }}
        """)
        custom_layout.addWidget(self.deps_list)
        
        # 创建按钮布局（水平排列）
        button_layout = QHBoxLayout()
        button_layout.setSpacing(self.get_scaled_size(5))  # 减少按钮间距
        custom_layout.addLayout(button_layout)
        
        # 添加模块按钮：用于添加Python模块依赖（支持批量添加）
        add_module_btn = NeumorphicButton("添加模块")
        add_module_btn.setFixedWidth(self.get_scaled_size(90))  # 减小按钮宽度
        add_module_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        add_module_btn.clicked.connect(self.add_module)  # 连接添加模块功能
        button_layout.addWidget(add_module_btn)
        
        # 添加资源按钮：用于添加数据文件、图片等资源（支持多选）
        add_resource_btn = NeumorphicButton("添加资源")
        add_resource_btn.setFixedWidth(self.get_scaled_size(90))  # 减小按钮宽度
        add_resource_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        add_resource_btn.clicked.connect(self.add_resource)  # 连接添加资源功能
        button_layout.addWidget(add_resource_btn)
        
        # 全选按钮：用于选择所有依赖项
        select_all_btn = NeumorphicButton("全选")
        select_all_btn.setFixedWidth(self.get_scaled_size(60))  # 减小按钮宽度
        select_all_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        select_all_btn.clicked.connect(self.select_all_dependencies)  # 连接全选功能
        button_layout.addWidget(select_all_btn)
        
        # 删除按钮：用于移除选中的依赖项（支持批量删除）
        remove_dep_btn = NeumorphicButton("删除")
        remove_dep_btn.setFixedWidth(self.get_scaled_size(60))  # 减小按钮宽度
        remove_dep_btn.setFixedHeight(self.get_scaled_size(32))  # 减小按钮高度
        remove_dep_btn.clicked.connect(self.remove_dependency)  # 连接删除依赖功能
        button_layout.addWidget(remove_dep_btn)
        
        # 添加使用提示信息 - 简化文本
        deps_tip = QLabel("提示: 支持Ctrl+点击和Shift+点击多选")
        deps_tip.setStyleSheet("color: #666666; font-size: 9pt;")
        custom_layout.addWidget(deps_tip)
        
        layout.addWidget(custom_group)
    
    def create_advanced_tab(self, tab):
        """创建高级设置标签页，包含编译器选择、优化选项、LTO链接优化、UPX压缩和并行编译等高级功能
        
        Args:
            tab: QTabWidget的标签页容器，用于放置高级设置相关的UI组件
        """
        # 设置标签页的主布局，使用垂直布局管理器
        layout = QVBoxLayout(tab)
        layout.setSpacing(self.get_scaled_size(3))  # 减小GroupBox之间的垂直间距
        layout.setContentsMargins(self.get_scaled_size(3), self.get_scaled_size(3), self.get_scaled_size(3), self.get_scaled_size(3))  # 减小边距
        
        # =========== 编译器选择和multiprocessing插件组（水平布局） ===========
        compiler_multiprocessing_layout = QHBoxLayout()
        compiler_multiprocessing_layout.setSpacing(self.get_scaled_size(5))  # 减小水平间距
        
        # 编译器选择组
        compiler_group = QGroupBox("编译器")
        compiler_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        compiler_layout = QVBoxLayout(compiler_group)
        compiler_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        compiler_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        
        # 创建编译器选项网格布局，每行两个选项
        compiler_grid_layout = QGridLayout()
        compiler_grid_layout.setSpacing(self.get_scaled_size(5))  # 设置选项间距
        
        # MSVC编译器选项（Windows平台推荐）
        self.msvc_rb = QRadioButton("MSVC")
        self.msvc_rb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.msvc_rb.setChecked(self.compiler_var == "msvc")  # 根据当前编译器变量设置选中状态
        self.msvc_rb.toggled.connect(lambda: self.update_compiler("msvc"))  # 连接编译器更新功能
        compiler_grid_layout.addWidget(self.msvc_rb, 0, 0)  # 第1行第1列
        
        # MinGW编译器选项（开源替代方案）
        self.mingw_rb = QRadioButton("MinGW")
        self.mingw_rb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.mingw_rb.setChecked(self.compiler_var == "mingw")  # 根据当前编译器变量设置选中状态
        self.mingw_rb.toggled.connect(lambda: self.update_compiler("mingw"))  # 连接编译器更新功能
        compiler_grid_layout.addWidget(self.mingw_rb, 0, 1)  # 第1行第2列
        
        # 添加平台限制说明
        platform_note = QLabel("(仅Windows平台)")
        platform_note.setStyleSheet("color: #666666; font-size: 9pt;")
        compiler_grid_layout.addWidget(platform_note, 1, 0)  # 第2行第1列
        
        # 将网格布局添加到编译器布局中
        compiler_layout.addLayout(compiler_grid_layout)
        compiler_multiprocessing_layout.addWidget(compiler_group)
        
        # multiprocessing插件组
        multiprocessing_group = QGroupBox("multiprocessing插件")
        multiprocessing_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        multiprocessing_layout = QVBoxLayout(multiprocessing_group)
        multiprocessing_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        multiprocessing_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        
        # multiprocessing插件启用选项
        self.multiprocessing_cb = QCheckBox("启用multiprocessing插件")
        self.multiprocessing_cb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        # self.multiprocessing_cb.setChecked(True)  # 默认启用multiprocessing插件
        self.multiprocessing_cb.setChecked(False)  # 默认启用multiprocessing插件
        self.multiprocessing_cb.toggled.connect(lambda state: setattr(self, 'multiprocessing_var', state))  # 更新multiprocessing_var变量
        multiprocessing_layout.addWidget(self.multiprocessing_cb)
        
        # multiprocessing插件说明
        multiprocessing_tip = QLabel("(多文件打包需启用)")
        multiprocessing_tip.setStyleSheet("color: #666666; font-size: 9pt;")
        multiprocessing_layout.addWidget(multiprocessing_tip)
        compiler_multiprocessing_layout.addWidget(multiprocessing_group)
        
        layout.addLayout(compiler_multiprocessing_layout)
        
        # =========== Python优化级别和UPX压缩组（水平布局） ===========
        opt_upx_layout = QHBoxLayout()
        opt_upx_layout.setSpacing(self.get_scaled_size(5))  # 减小水平间距
        
        # Python优化级别组
        opt_group = QGroupBox("Python优化级别")
        opt_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        # 使用垂直布局作为主布局
        main_opt_layout = QVBoxLayout(opt_group)
        main_opt_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        main_opt_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        
        # 优化级别说明
        # opt_note = QLabel("(Python标准优化)")
        # opt_note.setStyleSheet("color: #666666; font-size: 9pt;")
        # main_opt_layout.addWidget(opt_note)
        
        # 创建水平布局用于排列单选按钮
        opt_buttons_layout = QHBoxLayout()
        opt_buttons_layout.setSpacing(self.get_scaled_size(15))  # 设置按钮之间的水平间距
        main_opt_layout.addLayout(opt_buttons_layout)
        
        # 创建按钮组，确保优化级别选项互斥
        self.opt_group = QButtonGroup(self)
        
        # 无优化选项：不添加任何优化标志
        opt_rb0 = QRadioButton("无优化")
        opt_rb0.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        opt_rb0.setChecked(True)  # 默认选中无优化
        opt_rb0.toggled.connect(lambda: self.update_opt(0))  # 连接优化级别更新功能
        self.opt_group.addButton(opt_rb0)
        opt_buttons_layout.addWidget(opt_rb0)
        
        # 基本优化选项：使用-O标志，去除assert和__debug__代码
        opt_rb1 = QRadioButton("基本优化 (-O)")
        opt_rb1.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        # opt_rb1.setChecked(True)  # 注释掉的默认选中设置
        opt_rb1.toggled.connect(lambda: self.update_opt(1))  # 连接优化级别更新功能
        self.opt_group.addButton(opt_rb1)
        opt_buttons_layout.addWidget(opt_rb1)
        
        # 高级优化选项：使用-OO标志，同时去除docstring
        opt_rb2 = QRadioButton("高级优化 (-OO)")
        opt_rb2.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        opt_rb2.toggled.connect(lambda: self.update_opt(2))  # 连接优化级别更新功能
        self.opt_group.addButton(opt_rb2)
        opt_buttons_layout.addWidget(opt_rb2)
        
        # 添加拉伸因子，确保按钮均匀分布
        opt_buttons_layout.addStretch()
        
        opt_upx_layout.addWidget(opt_group, 1)  # 设置拉伸因子为1，平分空间
        
        # =========== LTO优化等级和调试选项组（水平布局） ===========
        lto_debug_layout = QHBoxLayout()
        lto_debug_layout.setSpacing(self.get_scaled_size(5))  # 减小水平间距
        
        # LTO链接优化
        lto_group = QGroupBox("LTO优化等级")
        lto_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        lto_layout = QVBoxLayout(lto_group)
        lto_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        lto_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        
        # LTO优化等级说明
        # lto_note = QLabel("(链接时优化)")
        # lto_note.setStyleSheet("color: #666666; font-size: 9pt;")
        # lto_layout.addWidget(lto_note)
        
        # 创建LTO优化等级按钮组
        self.lto_group = QButtonGroup(self)
        
        # 创建LTO选项网格布局，每行两个选项
        lto_grid_layout = QGridLayout()
        lto_grid_layout.setSpacing(self.get_scaled_size(5))  # 设置选项间距
        
        # 快速打包测试选项
        lto_off_rb = QRadioButton("快速打包 (--lto=off)")
        lto_off_rb.setToolTip("禁用LTO，打包速度最快，但运行性能较低")
        lto_off_rb.setFixedHeight(self.get_scaled_size(28))  # 设置统一高度
        lto_off_rb.toggled.connect(lambda: self.update_lto("off"))
        self.lto_group.addButton(lto_off_rb)
        lto_grid_layout.addWidget(lto_off_rb, 0, 0)  # 第1行第1列
        
        # 平衡性能与速度选项（默认）
        lto_yes_rb = QRadioButton("平衡性能 ✅ (--lto=yes)")
        lto_yes_rb.setToolTip("标准LTO优化，平衡打包速度和运行性能")
        lto_yes_rb.setFixedHeight(self.get_scaled_size(28))  # 设置统一高度
        lto_yes_rb.setChecked(True)  # 默认选中
        lto_yes_rb.toggled.connect(lambda: self.update_lto("yes"))
        self.lto_group.addButton(lto_yes_rb)
        lto_grid_layout.addWidget(lto_yes_rb, 0, 1)  # 第1行第2列
        
        # 大项目高效构建选项
        lto_thin_rb = QRadioButton("大项目 (--lto=full)")
        lto_thin_rb.setToolTip("轻量级LTO，适合大型项目，编译时间较短")
        lto_thin_rb.setFixedHeight(self.get_scaled_size(28))  # 设置统一高度
        lto_thin_rb.toggled.connect(lambda: self.update_lto("full"))
        self.lto_group.addButton(lto_thin_rb)
        lto_grid_layout.addWidget(lto_thin_rb, 1, 0)  # 第2行第1列
        
        # LTO优化注意事项
        lto_tip = QLabel("(需编译器支持)")
        lto_tip.setStyleSheet("color: #666666; font-size: 9pt;")
        lto_grid_layout.addWidget(lto_tip, 1, 1)  # 第2行第2列
        
        # 将网格布局添加到LTO布局中
        lto_layout.addLayout(lto_grid_layout)
        
        # 添加按钮组到布局中
        lto_debug_layout.addWidget(lto_group)
        
        # 调试选项组
        debug_group = QGroupBox("调试选项")
        debug_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        # 使用垂直布局作为主布局
        main_debug_layout = QVBoxLayout(debug_group)
        main_debug_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        main_debug_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        

        
        # 创建网格布局用于水平排列选项，每行两个
        debug_grid_layout = QGridLayout()
        debug_grid_layout.setSpacing(self.get_scaled_size(10))  # 设置选项间水平间距
        main_debug_layout.addLayout(debug_grid_layout)
        
        # 显示内存占用
        self.show_memory_cb = QCheckBox("显示内存占用")
        self.show_memory_cb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.show_memory_cb.setChecked(False)  # 默认关闭
        debug_grid_layout.addWidget(self.show_memory_cb, 0, 0)  # 第0行第0列
        
        # 显示被包含的模块列表
        self.show_modules_cb = QCheckBox("显示模块列表")
        self.show_modules_cb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.show_modules_cb.setChecked(False)  # 默认关闭
        debug_grid_layout.addWidget(self.show_modules_cb, 0, 1)  # 第0行第1列
        
        # 显示scons构建过程
        self.show_scons_cb = QCheckBox("显示构建过程")
        self.show_scons_cb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.show_scons_cb.setChecked(False)  # 默认关闭
        debug_grid_layout.addWidget(self.show_scons_cb, 1, 0)  # 第1行第0列
        
        # 显示详细输出日志
        self.verbose_cb = QCheckBox("详细输出日志")
        self.verbose_cb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.verbose_cb.setChecked(False)  # 默认关闭
        debug_grid_layout.addWidget(self.verbose_cb, 1, 1)  # 第1行第1列
        
        lto_debug_layout.addWidget(debug_group)
        layout.addLayout(lto_debug_layout)
        
        # UPX压缩组
        upx_group = QGroupBox("UPX 压缩")
        upx_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        upx_layout = QVBoxLayout(upx_group)
        upx_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        upx_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        
        # UPX压缩启用选项
        self.upx_cb = QCheckBox("启用UPX压缩")
        self.upx_cb.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        self.upx_cb.toggled.connect(self.toggle_upx)  # 连接UPX压缩切换功能
        upx_layout.addWidget(self.upx_cb)
        
        # UPX级别说明（Nuitka不支持UPX压缩级别设置）
        # level_note = QLabel("(压缩级别由UPX默认配置控制)")
        # level_note.setStyleSheet("color: #666666; font-size: 9pt;")
        # upx_layout.addWidget(level_note)
        
        # 保留变量以避免错误，但不再使用（兼容性考虑）
        self.upx_level = "best"
        
        # UPX路径设置区域
        path_layout = QHBoxLayout()
        path_layout.setSpacing(self.get_scaled_size(5))  # 减小按钮间距
        upx_layout.addLayout(path_layout)
        
        # UPX路径输入框
        self.upx_path_entry = QLineEdit()
        self.upx_path_entry.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        path_layout.addWidget(self.upx_path_entry, 1)  # 设置拉伸因子为1，占据主要空间
        
        # 浏览UPX文件按钮
        upx_browse = NeumorphicButton("浏览")
        upx_browse.setFixedWidth(self.get_scaled_size(80))  # 减小按钮宽度
        upx_browse.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        upx_browse.clicked.connect(self.browse_upx)  # 连接文件浏览功能
        path_layout.addWidget(upx_browse)
        
        # 设置PATH按钮：将UPX路径添加到系统环境变量
        upx_set_path = NeumorphicButton("设置 PATH")
        upx_set_path.setFixedWidth(self.get_scaled_size(80))  # 减小按钮宽度
        upx_set_path.setFixedHeight(self.get_scaled_size(28))  # 统一高度
        upx_set_path.clicked.connect(self.set_upx_path)  # 连接PATH设置功能
        path_layout.addWidget(upx_set_path)
        
        opt_upx_layout.addWidget(upx_group, 1)  # 设置拉伸因子为1，平分空间
        layout.addLayout(opt_upx_layout)
        
        # =========== 并行编译组 ===========
        jobs_group = QGroupBox("并行编译")
        jobs_group.setStyleSheet("""
            QGroupBox {
                border: 1px solid #CCCCCC;
                border-radius: 5px;
                margin-top: 10px;
                font-size: 10pt;
                background-color: #FAFAFA;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
        """)
        jobs_layout = QVBoxLayout(jobs_group)
        jobs_layout.setSpacing(self.get_scaled_size(2))  # 减小组件间距
        jobs_layout.setContentsMargins(self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5), self.get_scaled_size(5))  # 减小内边距
        
        # 显示当前任务数和CPU核心数
        self.jobs_label = QLabel(f"任务数: {self.jobs_var} / {os.cpu_count()}")
        self.jobs_label.setStyleSheet("color: #333333; font-size: 10pt;")
        jobs_layout.addWidget(self.jobs_label)
        
        # 并行任务数滑块控件
        self.jobs_slider = QSlider(Qt.Horizontal)
        self.jobs_slider.setMinimum(1)  # 最小1个任务
        self.jobs_slider.setMaximum(os.cpu_count())  # 最大不超过CPU核心数
        self.jobs_slider.setValue(self.jobs_var)  # 设置当前值
        self.jobs_slider.setFixedHeight(self.get_scaled_size(20))  # 统一高度
        self.jobs_slider.valueChanged.connect(self.update_jobs)  # 连接任务数更新功能
        jobs_layout.addWidget(self.jobs_slider)
        
        # 并行编译注意事项
        jobs_note = QLabel("(多任务加速编译，增加内存使用)")
        jobs_note.setStyleSheet("color: #666666; font-size: 9pt;")
        jobs_layout.addWidget(jobs_note)
        layout.addWidget(jobs_group)
        
        # 延迟初始化滚动位置，确保log_text控件完全初始化
        QTimer.singleShot(100, self._initialize_scroll_position)

    
    # ================= 通用方法 =================
    
    def browse_files(self, title, filter_text):
        """多文件浏览方法，支持选择多个文件
        
        Args:
            title (str): 文件对话框的标题
            filter_text (str): 文件过滤器，如"Python Files (*.py);;All Files (*)"
            
        Returns:
            list: 选择的文件路径列表，取消选择时返回空列表
        """
        try:
            # 多文件选择模式：选择多个现有文件
            paths, _ = QFileDialog.getOpenFileNames(
                self,
                title,
                "",
                filter_text
            )
            # 使用Windows系统默认的路径格式
            return paths
        except Exception as e:
            self.log_message(f"⛔ 文件选择失败: {str(e)}\n", "error")
            return []
    
    def browse_file(self, title, filter_text, widget, save=False, directory=False):
        """通用文件浏览方法，支持文件打开、保存和目录浏览
        
        Args:
            title (str): 文件对话框的标题
            filter_text (str): 文件过滤器，如"Python Files (*.py);;All Files (*)"
            widget: 要设置路径的UI控件（QLineEdit、QComboBox等）
            save (bool): 是否为保存模式，False为打开模式
            directory (bool): 是否为目录浏览模式
            
        Returns:
            str or None: 选择的文件/目录路径，取消选择时返回None
        """
        try:
            if directory:
                # 目录浏览模式：选择文件夹
                path = QFileDialog.getExistingDirectory(self, title)
                if path:
                    # 使用Windows系统默认的路径格式
                    # 根据控件类型设置路径文本
                    if hasattr(widget, 'setText'):
                        widget.setText(path)  # QLineEdit等文本控件
                    elif hasattr(widget, 'setCurrentText'):
                        widget.setCurrentText(path)  # QComboBox等下拉框控件
                return path
            elif save:
                # 文件保存模式：选择保存位置
                path, _ = QFileDialog.getSaveFileName(
                    self, 
                    title, 
                    "", 
                    filter_text
                )
                if path:
                    # 使用Windows系统默认的路径格式
                    # 根据控件类型设置路径文本
                    if hasattr(widget, 'setText'):
                        widget.setText(path)
                    elif hasattr(widget, 'setCurrentText'):
                        widget.setCurrentText(path)
                return path
            else:
                # 文件打开模式：选择现有文件
                path, _ = QFileDialog.getOpenFileName(
                    self, 
                    title, 
                    "", 
                    filter_text
                )
                if path:
                    # 使用Windows系统默认的路径格式
                    # 根据控件类型设置路径文本
                    if hasattr(widget, 'setText'):
                        widget.setText(path)
                    elif hasattr(widget, 'setCurrentText'):
                        widget.setCurrentText(path)
                return path
        except Exception as e:
            # 异常处理：记录错误日志
            self.log_message(f"⚠ 文件浏览错误: {str(e)}\n", "warning")
            return None
    
    def browse_script(self):
        """浏览并选择Python主脚本文件
        
        该方法会自动设置输出目录和可执行文件名：
        - 输出目录设置为脚本所在目录下的dist文件夹
        - 可执行文件名设置为脚本名称（Windows平台添加.exe后缀）
        """
        # 记录用户操作
        self.log_user_action("浏览脚本文件", "开始选择Python主脚本")
        
        # 调用通用文件浏览方法选择Python脚本
        path = self.browse_file(
            "选择 Python 主脚本",
            "Python Files (*.py);;All Files (*)",
            self.script_entry
        )
        if path:
            # 记录用户操作
            self.log_user_action("选择脚本文件", f"路径: {path}")
            
            # 使用Windows系统默认的路径格式
            
            # 设置输出目录为脚本所在目录/dist
            script_dir = os.path.dirname(path)  # 获取脚本所在目录
            dist_dir = os.path.join(script_dir, "dist")  # 创建dist目录路径
            # 使用Windows系统默认的路径格式
            self.output_entry.setText(dist_dir)  # 设置输出目录
            
            # 自动设置可执行文件名为脚本名称
            name = os.path.splitext(os.path.basename(path))[0]  # 去除文件扩展名
            if self.platform_var == "windows":
                name += ".exe"  # Windows平台添加.exe后缀
            self.name_entry.setText(name)  # 设置可执行文件名
            
            # 记录自动设置操作
            self.log_user_action("自动设置输出目录", f"目录: {dist_dir}")
            self.log_user_action("自动设置可执行文件名", f"名称: {name}")
    
    def browse_output(self):
        """浏览并选择输出目录
        
        用于选择打包后可执行文件的输出位置
        """
        # 记录用户操作
        self.log_user_action("浏览输出目录", "开始选择输出目录")
        
        # 获取当前输出目录
        current_dir = self.output_entry.text().strip()
        
        # 调用通用文件浏览方法选择目录
        self.browse_file(
            "选择输出目录",
            "",  # 目录浏览不需要文件过滤器
            self.output_entry,
            directory=True  # 设置为目录浏览模式
        )
        
        # 检查目录是否发生变化
        new_dir = self.output_entry.text().strip()
        if new_dir != current_dir and new_dir:
            # 记录用户操作
            self.log_user_action("更改输出目录", f"新目录: {new_dir}")
    
    def browse_icon(self):
        """浏览并选择应用程序图标文件
        
        支持ICO格式和常见图片格式（PNG、JPG、JPEG）
        """
        # 记录用户操作
        self.log_user_action("浏览图标文件", "开始选择应用程序图标")
        
        # 获取当前图标文件
        current_icon = self.icon_entry.text().strip()
        
        # 调用通用文件浏览方法选择图标文件
        self.browse_file(
            "选择应用程序图标",
            "Icon Files (*.ico);;Image Files (*.png *.jpg *.jpeg)",
            self.icon_entry
        )
        
        # 检查图标文件是否发生变化
        new_icon = self.icon_entry.text().strip()
        if new_icon != current_icon and new_icon:
            # 记录用户操作
            self.log_user_action("更改应用程序图标", f"新图标: {new_icon}")
    
    def browse_upx(self):
        """浏览并选择UPX可执行文件
        
        UPX是一个可执行文件压缩工具，用于减小打包后的文件体积
        """
        # 调用通用文件浏览方法选择UPX文件
        self.browse_file(
            "选择 UPX 可执行文件",
            "Executable Files (*.exe);;All Files (*)",
            self.upx_path_entry
        )
    
    def browse_python(self):
        """浏览并选择Python解释器路径或虚拟环境文件夹
        
        根据操作系统平台自动调整文件过滤器：
        - 支持选择Python可执行文件(.exe)
        - 支持选择虚拟环境文件夹，自动检测其中的Python解释器
        - 确保选择的Python环境（即使未添加系统环境变量）也能被正确使用
        """
        # 创建文件对话框，使用Windows原生样式
        dialog = QFileDialog(self, "选择Python解释器或虚拟环境文件夹")
        dialog.setOption(QFileDialog.DontUseNativeDialog, False)
        
        # 允许选择文件和文件夹
        dialog.setFileMode(QFileDialog.ExistingFiles)
        
        # 创建文件过滤器
        if platform.system() == "Windows":
            file_filter = "Python Executable (python.exe);;All Files (*)"
        else:
            file_filter = "Python Executable (python*);;All Files (*)"
        dialog.setNameFilter(file_filter)
        
        # 显示对话框
        if dialog.exec():
            selected_paths = dialog.selectedFiles()
            if selected_paths:
                path = selected_paths[0]
                
                # 检查选择的是文件还是文件夹
                if os.path.isdir(path):
                    # 选择的是文件夹，尝试自动检测其中的Python解释器
                    python_exe = self._detect_python_in_virtual_env(path)
                    if python_exe:
                        # 如果找到有效的Python解释器，将其设置到下拉框中
                        if hasattr(self.python_combo, 'setCurrentText'):
                            # 对于不可编辑的下拉框，需要先检查路径是否已存在
                            if python_exe not in [self.python_combo.itemText(i) for i in range(self.python_combo.count())]:
                                self.python_combo.addItem(python_exe)
                            self.python_combo.setCurrentText(python_exe)
                        
                        # 验证Python解释器是否可用
                        if self._verify_python_interpreter(python_exe):
                            self.log_message(f"✓ 成功验证Python解释器: {python_exe}\n", "success")
                        else:
                            self.log_message(f"⚠ 警告：Python解释器可能无法正常使用: {python_exe}\n", "warning")
                        
                        # 记录用户操作
                        self.log_user_action("选择虚拟环境文件夹", f"路径: {path}, 检测到Python: {python_exe}")
                    else:
                        # 未找到有效的Python解释器
                        self.log_message(f"⚠ 在选择的文件夹中未找到有效的Python解释器: {path}\n", "warning")
                else:
                    # 选择的是文件，设置到下拉框中
                    if hasattr(self.python_combo, 'setCurrentText'):
                        # 对于不可编辑的下拉框，需要先检查路径是否已存在
                        if path not in [self.python_combo.itemText(i) for i in range(self.python_combo.count())]:
                            self.python_combo.addItem(path)
                        self.python_combo.setCurrentText(path)
                    
                    # 验证Python解释器是否可用
                    if self._verify_python_interpreter(path):
                        self.log_message(f"✓ 成功验证Python解释器: {path}\n", "success")
                    else:
                        self.log_message(f"⚠ 警告：Python解释器可能无法正常使用: {path}\n", "warning")
                    
                    # 记录用户操作
                    self.log_user_action("选择Python解释器", f"路径: {path}")
        
    def _detect_python_in_virtual_env(self, env_dir):
        """检测虚拟环境文件夹中的Python解释器
        
        Args:
            env_dir (str): 虚拟环境文件夹路径
            
        Returns:
            str or None: 有效的Python解释器路径，未找到则返回None
        """
        # 记录开始检测
        self.log_message(f"🔍 开始检测虚拟环境中的Python解释器: {env_dir}\n", "info")
        
        # 根据操作系统平台检测可能的Python解释器路径
        if platform.system() == "Windows":
            # Windows系统常见的Python解释器路径
            possible_paths = [
                os.path.join(env_dir, 'Scripts', 'python.exe'),  # 标准虚拟环境
                os.path.join(env_dir, 'python.exe'),  # conda环境或其他特殊环境
                os.path.join(env_dir, 'bin', 'python.exe')  # 某些非标准环境
            ]
        else:
            # Linux/macOS系统常见的Python解释器路径
            possible_paths = [
                os.path.join(env_dir, 'bin', 'python'),
                os.path.join(env_dir, 'bin', 'python3'),
                os.path.join(env_dir, 'python')
            ]
        
        # 遍历所有可能的路径，查找有效的Python解释器
        for python_path in possible_paths:
            if os.path.isfile(python_path):
                # 检查是否为有效的虚拟环境
                if self._is_valid_virtual_environment(python_path):
                    self.log_message(f"✓ 找到有效的虚拟环境Python解释器: {python_path}\n", "success")
                    return python_path
                else:
                    self.log_message(f"⚠ 找到Python解释器但不是有效的虚拟环境: {python_path}\n", "warning")
        
        # 遍历所有子目录，尝试找到python.exe（对于可能的特殊环境结构）
        for root, _, files in os.walk(env_dir):
            # 限制搜索深度，避免性能问题
            depth = root[len(env_dir):].count(os.sep)
            if depth > 3:
                continue
            
            # 查找python.exe（Windows）或python/python3（Linux/macOS）
            if platform.system() == "Windows":
                if 'python.exe' in files:
                    python_path = os.path.join(root, 'python.exe')
                    if self._is_valid_virtual_environment(python_path):
                        self.log_message(f"✓ 在子目录中找到有效的虚拟环境Python解释器: {python_path}\n", "success")
                        return python_path
            else:
                for file in files:
                    if file in ['python', 'python3'] and not file.endswith('.py'):
                        python_path = os.path.join(root, file)
                        if self._is_valid_virtual_environment(python_path):
                            self.log_message(f"✓ 在子目录中找到有效的虚拟环境Python解释器: {python_path}\n", "success")
                            return python_path
        
        # 未找到有效的Python解释器
        self.log_message(f"⚠ 未在文件夹中找到有效的虚拟环境Python解释器: {env_dir}\n", "warning")
        return None
    
    def start_python_detection(self, silent=True, force=False):
        """启动Python环境检测后台线程
        
        Args:
            silent (bool): 是否静默模式，不显示进度信息
            force (bool): 是否强制重新检测，忽略缓存
        """
        # 检查是否已有Python检测线程在运行
        if hasattr(self, 'python_detection_thread') and self.python_detection_thread and self.python_detection_thread.isRunning():
            if not silent:
                self.log_message("⚠ Python环境检测已在进行中...\n", "warning")
            return
            
        # 创建后台线程执行检测
        thread = PythonDetectionThread(parent=None, silent=silent, force=force)
        self.python_detection_thread = thread  # 保存线程引用
        
        # 连接信号
        thread.detection_completed.connect(self._on_python_detection_completed)
        thread.detection_failed.connect(self._on_python_detection_failed)
        thread.progress_updated.connect(self._on_python_detection_progress)
        thread.log_message.connect(self.log_message)
        
        # 启动线程
        thread.start()
        
        # 如果不是静默模式，显示检测开始信息
        if not silent:
            self.log_message("🔍 开始Python环境检测...\n", "info")
            

    
    def _on_python_detection_completed(self, python_paths, from_cache=False):
        """Python检测完成回调
        
        Args:
            python_paths (list): 检测到的Python路径列表
            from_cache (bool): 是否从缓存读取的结果
        """
        # 清理线程引用
        if hasattr(self, 'python_detection_thread'):
            self.python_detection_thread = None
            
        if python_paths:
            self.log_message(f"✓ Python环境检测完成，共找到 {len(python_paths)} 个Python环境\n", "success")
            
            # 只在真正执行了检测（而不是从缓存读取）时才保存缓存
            if not from_cache:
                try:
                    cache_key = self._get_cache_key({})
                    self._save_to_cache(cache_key, python_paths)
                    self._update_detection_timestamp()
                    self.log_message("✅ Python环境检测结果已保存到缓存\n", "success")
                except Exception as e:
                    self.log_message(f"⚠ 保存缓存失败: {str(e)}\n", "warning")
            else:
                self.log_message("✅ 使用缓存的Python环境检测结果，无需重新保存\n", "success")
            
            # 更新下拉框
            current_text = self.python_combo.currentText()
            self.python_combo.clear()
            
            # 添加检测到的Python路径
            for path in python_paths:
                self.python_combo.addItem(path)
                self.log_message(f"  - {path}\n", "info")
            
            # 尝试恢复之前的选择
            index = self.python_combo.findText(current_text)
            if index >= 0:
                self.python_combo.setCurrentIndex(index)
                self.log_message(f"✓ 恢复之前的选择: {current_text}\n", "success")
            elif python_paths:
                self.python_combo.setCurrentIndex(0)
                selected_path = python_paths[0]
                self.log_message(f"✓ 默认选择: {selected_path}\n", "success")
                
            # 如果有多个Python环境，提示用户可以选择
            if len(python_paths) > 1:
                self.log_message("💡 您可以通过下拉框选择其他Python环境\n", "info")
        else:
            self.log_message("⚠ 未检测到Python环境\n", "warning")
    
    def _on_python_detection_failed(self, error_msg):
        """Python检测失败回调
        
        Args:
            error_msg (str): 错误信息
        """
        # 清理线程引用
        if hasattr(self, 'python_detection_thread'):
            self.python_detection_thread = None
            
        self.log_message(f"⛔ Python环境检测失败: {error_msg}\n", "error")
    
    def _on_python_detection_progress(self, message):
        """Python检测进度更新回调
        
        Args:
            message (str): 进度信息
        """
        self.log_message(message, "info")
    



    
    def auto_detect_python(self, silent=True, force=False):
        """从系统环境变量自动检测Python，包括虚拟环境
        
        该方法执行全面的Python环境检测，包括：
        1. 检查环境管理器相关环境变量（Conda、Miniconda等）
        2. 扫描PATH环境变量中的Python可执行文件
        3. 检查常见Python安装目录
        4. 基于已找到的Python路径检测相关虚拟环境
        5. 检测独立的虚拟环境
        
        Args:
            silent (bool): 是否静默检测，True时不弹出选择对话框，
                          False时允许多个Python环境供用户选择
            force (bool): 是否强制重新检测，True时忽略缓存重新检测
        """
        import glob
        
        # 显示加载状态
        self.log_message("🔍 开始检测Python环境...\n", "info")
        
        # 增加检测计数
        self.total_detection_count += 1
        
        # 生成缓存键（基于环境变量和系统状态的缓存）
        cache_params = {
            'path': os.environ.get('PATH', ''),
            'conda_home': os.environ.get('CONDA_HOME', ''),
            'python_home': os.environ.get('PYTHON_HOME', ''),
            'programfiles': os.environ.get('PROGRAMFILES', ''),
            'programfiles_x86': os.environ.get('PROGRAMFILES(X86)', ''),
            'localappdata': os.environ.get('LOCALAPPDATA', ''),
            'conda_prefix': os.environ.get('CONDA_PREFIX', ''),
            'miniconda_home': os.environ.get('MINICONDA_HOME', ''),
            'miniforge_home': os.environ.get('MINIFORGE_HOME', ''),
            'mamba_home': os.environ.get('MAMBA_HOME', '')
        }
        cache_key = self._get_cache_key(cache_params)
        
        # 如果不是强制检测，尝试从缓存加载结果
        if not force:
            cached_result = self._load_from_cache(cache_key)
            if cached_result:
                # 检查缓存是否仍然有效
                if self._is_cache_valid(cached_result):
                    self.log_message("✅ 使用缓存的Python环境检测结果\n", "success")
                    python_paths = cached_result
                    # 使用缓存时不需要重新保存
                else:
                    self.log_message("🔄 环境已变更，重新检测Python环境...\n", "info")
                    # 缓存已失效，执行完整检测
                    python_paths = self._perform_full_detection()
                    # 更新缓存
                    self._save_to_cache(cache_key, python_paths)
            else:
                # 没有缓存，执行完整检测
                self.log_message("🔍 开始检测Python环境...\n", "info")
                python_paths = self._perform_full_detection()
                # 保存到缓存
                self._save_to_cache(cache_key, python_paths)
        else:
            # 强制重新检测，忽略缓存
            self.log_message("🔄 强制重新检测Python环境...\n", "info")
            python_paths = self._perform_full_detection()
            # 更新缓存
            self._save_to_cache(cache_key, python_paths)
        
        self.log_message(f"🔍 Python检测完成，共找到 {len(python_paths)} 个Python环境\n", "info")
        
        # 如果不是静默模式，更新UI
        if not silent:
            if python_paths:
                # 保存当前选中的Python路径（如果有）
                current_path = self.python_combo.currentText() if self.python_combo.count() > 0 else ""
                
                # 阻止信号触发，避免在更新下拉框时触发on_python_combo_changed
                self.python_combo.blockSignals(True)
                
                try:
                    # 清空下拉框并添加所有检测到的Python环境
                    self.python_combo.clear()
                    for path in python_paths:
                        self.python_combo.addItem(path)
                    
                    # 非静默模式：如果有多个Python，选择第一个，但用户可以通过下拉框选择其他
                    if len(python_paths) > 1:
                        selected_path = python_paths[0]
                        self.python_combo.setCurrentText(selected_path)
                        self.log_message(f"✓ 自动检测到 {len(python_paths)} 个Python环境，已选择: {selected_path}\n", "success")
                        self.log_message("💡 您可以通过下拉框选择其他Python环境\n", "info")
                    else:
                        # 只找到一个Python，直接使用
                        self.python_combo.setCurrentText(python_paths[0])
                        self.log_message(f"✓ 自动检测到Python: {python_paths[0]}\n", "success")
                finally:
                    # 恢复信号触发
                    self.python_combo.blockSignals(False)
                    
                # 如果之前有选中的路径，检查是否还在新列表中
                if current_path and current_path in python_paths:
                    # 如果之前的路径还在新列表中，恢复选择（在信号阻塞状态下）
                    self.python_combo.blockSignals(True)
                    try:
                        self.python_combo.setCurrentText(current_path)
                        self.log_message(f"🔄 恢复之前选择的Python环境: {current_path}\n", "info")
                    finally:
                        self.python_combo.blockSignals(False)
            else:
                # 没有检测到Python的情况处理
                QMessageBox.warning(self, "检测失败", "未检测到系统中的Python解释器，请手动选择安装路径。")
                self.log_message("⚠ 未检测到系统中的Python解释器\n", "warning")
        
        # 在所有情况下都返回检测到的Python路径列表
        return python_paths
    
    def _get_cache_key(self, cache_params):
        """生成缓存键
        
        Args:
            cache_params (dict): 缓存参数
            
        Returns:
            str: 生成的缓存键
        """
        # 基于环境变量和系统状态生成缓存键
        try:
            # 包含所有重要的环境变量
            env_info = [
                cache_params.get('path', ''),
                cache_params.get('conda_home', ''),
                cache_params.get('python_home', ''),
                cache_params.get('programfiles', ''),
                cache_params.get('programfiles_x86', ''),
                cache_params.get('localappdata', ''),
                cache_params.get('conda_prefix', ''),
                cache_params.get('miniconda_home', ''),
                cache_params.get('miniforge_home', ''),
                cache_params.get('mamba_home', '')
            ]
            
            # 添加系统信息
            env_info.extend([
                platform.system(),
                platform.architecture()[0],
                sys.version
            ])
            
            env_str = '|'.join(env_info)
            cache_key = hashlib.md5(env_str.encode()).hexdigest()[:8]
            return f"python_paths_{cache_key}"
            
        except Exception as e:
            self.log_message(f"⚠ 生成缓存键失败: {e}\n", "warning")
            return "python_paths_cache"
    
    def _load_from_cache(self, cache_key):
        """从缓存加载结果
        
        Args:
            cache_key (str): 缓存键
            
        Returns:
            object: 缓存的数据，如果缓存不存在则返回None
        """
        import os
        import pickle
        
        # 使用固定缓存文件名
        cache_file = os.path.join(self.cache_dir, "python_paths_cache.pkl")
        self.log_message(f"🔍 尝试从缓存加载: {cache_file}\n", "info")
        if os.path.exists(cache_file):
            try:
                with open(cache_file, 'rb') as f:
                    data = pickle.load(f)
                self.log_message(f"✅ 缓存加载成功: {cache_file}\n", "success")
                return data
            except Exception as e:
                self.log_message(f"⚠ 缓存加载失败: {e}\n", "warning")
        else:
            self.log_message(f"⚠ 缓存文件不存在: {cache_file}\n", "warning")
        return None
    
    def _save_to_cache(self, cache_key, data):
        """保存结果到缓存
        
        Args:
            cache_key (str): 缓存键
            data (object): 要缓存的数据
        """
        import os
        import pickle
        
        # 使用固定缓存文件名
        cache_file = os.path.join(self.cache_dir, "python_paths_cache.pkl")
        try:
            # 确保缓存目录存在
            # self.log_message(f"🔍 确保缓存目录存在: {self.cache_dir}\n", "info")
            os.makedirs(self.cache_dir, exist_ok=True)
            self.log_message(f"✅ 缓存目录已创建或已存在: {self.cache_dir}\n", "success")
            
            # 保存缓存文件
            # self.log_message(f"🔍 保存缓存文件: {cache_file}\n", "info")
            with open(cache_file, 'wb') as f:
                pickle.dump(data, f)
            self.log_message(f"✅ 缓存保存成功: {cache_file}\n", "success")
        except PermissionError as e:
            self.log_message(f"⚠ 缓存保存失败（权限不足）: {e}\n", "error")
        except OSError as e:
            self.log_message(f"⚠ 缓存保存失败（文件系统错误）: {e}\n", "error")
        except Exception as e:
            self.log_message(f"⚠ 缓存保存失败（未知错误）: {e}\n", "error")
    
    def _is_cache_valid(self, cached_paths):
        """检查缓存是否仍然有效
        
        通过检查虚拟环境目录的修改时间、环境变量变化来验证缓存的有效性。
        如果任何虚拟环境目录的修改时间在上次检测之后，或环境变量发生显著变化，则缓存失效。
        同时检查环境管理器的envs目录，以检测新增或删除的虚拟环境。
        
        Args:
            cached_paths (list): 缓存的Python路径列表
            
        Returns:
            bool: 如果缓存有效返回True，否则返回False
        """
        self.log_message("🔍 开始验证缓存有效性...\n", "info")
        
        # 确保cached_paths是一个列表
        if not isinstance(cached_paths, list):
            self.log_message(f"⚠ 缓存数据类型错误: {type(cached_paths)}，期望list\n", "warning")
            return False
        
        # 获取上次检测的时间戳文件
        timestamp_file = os.path.join(self.cache_dir, "last_detection_timestamp.txt")
        if not os.path.exists(timestamp_file):
            self.log_message("⚠ 检测时间戳文件不存在，缓存无效\n", "warning")
            return False
        
        try:
            with open(timestamp_file, 'r') as f:
                last_detection_time = float(f.read().strip())
            self.log_message(f"✅ 读取检测时间戳: {last_detection_time:.6f}\n", "success")
        except Exception as e:
            self.log_message(f"⚠ 读取检测时间戳失败: {e}\n", "warning")
            return False
        
        # 增加5分钟的容差，避免频繁失效
        tolerance = 300.0
        
        # 检查环境变量变化和虚拟环境路径存在性
        try:
            # 检查VIRTUAL_ENV环境变量是否发生变化
            # 计算当前PATH环境变量的哈希值，与缓存中的进行比较
            import hashlib
            current_path_hash = hashlib.md5(os.environ.get('PATH', '').encode()).hexdigest()
            
            # 检查缓存中是否存在'my_venv_nuitka'虚拟环境
            virtual_env_in_cache = False
            for path in cached_paths:
                if 'my_venv_nuitka' in path.lower():
                    virtual_env_in_cache = True
                    
                    # 直接检查该路径是否存在
                    if not os.path.exists(path):
                        self.log_message(f"🔄 检测到已删除的虚拟环境路径: {path}\n", "info")
                        return False
                    
                    # 检查该路径是否在当前PATH环境变量中
                    if path not in os.environ.get('PATH', '') and not os.environ.get('VIRTUAL_ENV', ''):
                        self.log_message(f"🔄 虚拟环境路径 {path} 不再在PATH环境变量中\n", "info")
                        return False
                    
            # 检查当前环境中是否存在这个特定的虚拟环境路径
            current_virtual_env = os.environ.get('VIRTUAL_ENV', '')
            
            # 如果缓存中有这个虚拟环境，但当前环境中不存在，则缓存失效
            if virtual_env_in_cache and not current_virtual_env:
                self.log_message(f"🔄 检测到环境变量变化：缓存中存在虚拟环境路径但当前环境中不存在\n", "info")
                return False
        except Exception as e:
            self.log_message(f"⚠ 检查环境变量变化时出错: {e}\n", "warning")
        
        # 检查每个Python路径的虚拟环境目录修改时间
        for path in cached_paths:
            self.log_message(f"🔍 检查Python路径: {path}\n", "info")
            # 获取虚拟环境根目录
            env_root = self._get_virtual_env_root(path)
            if env_root and os.path.exists(env_root):
                self.log_message(f"🔍 虚拟环境根目录: {env_root}\n", "info")
                # 检查目录的修改时间
                try:
                    mtime = os.path.getmtime(env_root)
                    self.log_message(f"✅ 虚拟环境修改时间: {mtime:.6f}\n", "success")
                    self.log_message(f"🔍 比较时间戳: {mtime:.6f} > {last_detection_time:.6f}\n", "info")
                    if mtime > last_detection_time - tolerance:
                        # 如果目录修改时间在上次检测之前1秒内或之后，缓存失效
                        self.log_message(f"🔄 虚拟环境 {env_root} 已变更\n", "info")
                        return False
                except Exception as e:
                    self.log_message(f"⚠ 检查虚拟环境修改时间失败: {e}\n", "warning")
                    continue
            else:
                self.log_message(f"⚠ 未找到虚拟环境根目录或路径不存在: {env_root}\n", "warning")
        
        # 检查环境管理器的envs目录修改时间，以检测新增或删除的虚拟环境
        env_managers = self._get_env_managers()
        for manager in env_managers:
            envs_dir = os.path.join(manager['path'], 'envs')
            if os.path.exists(envs_dir):
                try:
                    envs_mtime = os.path.getmtime(envs_dir)
                    self.log_message(f"🔍 环境管理器envs目录: {envs_dir}, 修改时间: {envs_mtime:.6f}\n", "info")
                    self.log_message(f"🔍 比较时间戳: {envs_mtime:.6f} > {last_detection_time:.6f}\n", "info")
                    if envs_mtime > last_detection_time - tolerance:
                        self.log_message(f"🔄 环境管理器 {manager['path']} 的envs目录已变更\n", "info")
                        return False
                except Exception as e:
                    self.log_message(f"⚠ 检查环境管理器envs目录修改时间失败: {e}\n", "warning")
                    continue
        
        self.log_message("✅ 缓存验证通过，缓存有效\n", "success")
        return True
    
    def _get_env_managers(self):
        """获取已安装的Python环境管理器信息
        
        Returns:
            list: 包含环境管理器信息的列表，每个元素是包含type、path和source键的字典
        """
        import os
        
        env_managers = []  # 存储找到的环境管理器信息
        
        # 首先从环境变量获取Python环境管理器路径
        env_vars_to_check = [
            ('CONDA_PREFIX', 'conda'),      # Conda环境前缀（指向具体环境）
            ('CONDA_HOME', 'conda'),        # Conda主目录
            ('MINICONDA_HOME', 'miniconda'), # Miniconda主目录
            ('MINIFORGE_HOME', 'miniforge'), # Miniforge主目录
            ('MAMBA_HOME', 'mamba')         # Mamba主目录
        ]
        
        # 遍历环境变量，查找已安装的环境管理器
        for env_var, manager_type in env_vars_to_check:
            if env_var in os.environ:
                if env_var == 'CONDA_PREFIX':
                    # CONDA_PREFIX指向的是具体环境，需要获取基础目录
                    conda_prefix = os.environ[env_var]
                    # 检查是否在envs目录下，如果是，需要向上两级目录获取基础目录
                    if 'envs' in conda_prefix:
                        # 如果在envs目录下，说明是conda虚拟环境，需要向上两级获取conda安装根目录
                        base_path = os.path.dirname(os.path.dirname(conda_prefix))  # 从 envs/env_name 向上两级
                    else:
                        # 否则直接向上一级获取基础目录（可能是base环境）
                        base_path = os.path.dirname(conda_prefix)
                    
                    # 如果基础目录不包含miniforge3或anaconda3等，尝试向上查找
                    if not any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                        # 尝试在当前目录下查找这些目录
                        parent_dir = base_path
                        for _ in range(3):  # 最多向上查找3级目录
                            for name in ['miniforge3', 'anaconda3', 'miniconda3']:  # 常见的conda发行版目录名
                                test_path = os.path.join(parent_dir, name)  # 构建测试路径
                                if os.path.exists(test_path):  # 检查路径是否存在
                                    base_path = test_path  # 更新为基础路径
                                    break  # 找到后跳出内层循环
                            if any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                                break  # 找到有效的conda安装目录后跳出外层循环
                            parent_dir = os.path.dirname(parent_dir)  # 继续向上查找
                else:
                    # 对于其他环境变量，直接使用环境变量指向的路径作为基础路径
                    base_path = os.environ[env_var]  # 直接使用环境变量指向的路径
                
                # 将找到的环境管理器信息添加到列表
                env_managers.append({
                    'type': manager_type,
                    'path': base_path,
                    'source': f'环境变量 {env_var}'
                })
        
        # 如果没有从环境变量找到，搜索常见的安装路径
        if not env_managers:
            # 常见的Python环境管理器安装路径（覆盖多种安装位置）
            common_manager_paths = [
                # Miniconda3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniconda3'), 'miniconda'),
                # Miniconda3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniconda3'), 'miniconda'),
                # Miniconda3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniconda3'), 'miniconda'),
                
                # Anaconda3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Anaconda3'), 'anaconda'),
                # Anaconda3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Anaconda3'), 'anaconda'),
                # Anaconda3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Anaconda3'), 'anaconda'),
                
                # Miniforge3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniforge3'), 'miniforge'),
                # Miniforge3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniforge3'), 'miniforge'),
                # Miniforge3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniforge3'), 'miniforge'),
                
                # Mambaforge - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Mambaforge'), 'mamba'),
                # Mambaforge - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Mambaforge'), 'mamba'),
                # Mambaforge - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Mambaforge'), 'mamba'),
                
                # 用户主目录下的安装（手动安装到用户目录）
                (os.path.join(os.path.expanduser('~'), 'miniconda3'), 'miniconda'),
                (os.path.join(os.path.expanduser('~'), 'anaconda3'), 'anaconda'),
                (os.path.join(os.path.expanduser('~'), 'miniforge3'), 'miniforge'),
                (os.path.join(os.path.expanduser('~'), 'mambaforge'), 'mamba'),
                
                # 常见自定义安装路径（特定软件安装目录）
                ('F:\\itsoft\\miniforge3', 'miniforge'),
                ('C:\\itsoft\\miniforge3', 'miniforge'),
                ('D:\\itsoft\\miniforge3', 'miniforge'),
                ('E:\\itsoft\\miniforge3', 'miniforge')
            ]
                
            # 遍历所有常见安装路径，查找存在的环境管理器
            for manager_path, manager_type in common_manager_paths:
                if os.path.exists(manager_path):
                    env_managers.append({
                        'type': manager_type,
                        'path': manager_path,
                        'source': '常见安装路径'
                    })
        
        return env_managers
    
    def _get_virtual_env_root(self, python_path):
        """获取Python路径对应的虚拟环境根目录
        
        Args:
            python_path (str): Python可执行文件路径
            
        Returns:
            str: 虚拟环境根目录路径，如果不是虚拟环境则返回None
        """
        # 检查是否为虚拟环境中的Python
        # 虚拟环境的Python通常在Scripts目录下（Windows）
        if "Scripts" in python_path and python_path.endswith("python.exe"):
            # 获取Scripts目录的父目录
            scripts_dir = os.path.dirname(python_path)
            env_root = os.path.dirname(scripts_dir)
            # 验证是否为有效的虚拟环境
            if self._is_valid_virtual_environment(env_root):
                return env_root
        
        # 检查是否为conda环境
        # conda环境的Python通常在envs目录下
        if "envs" in python_path:
            # 向上查找直到找到envs目录
            parts = python_path.split(os.sep)
            for i in range(len(parts) - 1, -1, -1):
                if parts[i] == "envs":
                    # envs目录的父目录是conda根目录
                    conda_root = os.sep.join(parts[:i])
                    env_name = parts[i+1] if i+1 < len(parts) else ""
                    if env_name:
                        env_root = os.path.join(conda_root, "envs", env_name)
                        if self._is_valid_virtual_environment(env_root):
                            return env_root
        
        return None
    
    def _perform_full_detection(self):
        """执行完整的Python环境检测
        
        执行与之前相同的检测逻辑，但作为一个独立的方法。
        
        Returns:
            list: 检测到的Python路径列表
        """
        import glob
        import time
        
        # 记录开始时间用于性能监控
        start_time = time.time()
        
        # 首先基于系统环境变量检测已安装的Python
        python_paths = []
        
        self.log_message("🔍 开始检测系统Python环境...\n", "info")
        
        # 1. 检查Python环境管理器相关的环境变量
        # 定义需要检查的环境变量及其对应的管理器类型
        env_vars_to_check = [
            ('CONDA_PREFIX', 'conda'),      # Conda当前环境路径
            ('CONDA_HOME', 'conda'),       # Conda安装根目录
            ('MINICONDA_HOME', 'miniconda'), # Miniconda安装目录
            ('MINIFORGE_HOME', 'miniforge'), # Miniforge安装目录
            ('MAMBA_HOME', 'mamba'),       # Mamba安装目录
            ('PYTHON_HOME', 'python'),     # Python安装目录
            ('PYTHONPATH', 'python')       # Python模块搜索路径
        ]
        
        # 遍历环境变量列表，检查每个环境变量是否存在
        for env_var, manager_type in env_vars_to_check:
            if env_var in os.environ:
                env_value = os.environ[env_var]
                self.log_message(f"🔍 发现环境变量 {env_var}: {env_value}\n", "info")
                
                if env_var == 'CONDA_PREFIX':
                    # CONDA_PREFIX指向的是具体环境，直接使用
                    python_exe = os.path.join(env_value, 'python.exe')
                    if os.path.isfile(python_exe):
                        python_paths.append(python_exe)
                        self.log_message(f"✓ 从CONDA_PREFIX找到Python: {python_exe}\n", "success")
                elif env_var == 'PYTHONPATH':
                    # PYTHONPATH是模块搜索路径，不是Python安装路径，跳过处理
                    continue
                else:
                    # 其他环境变量指向的是基础目录
                    base_path = env_value
                    # 检查基础Python可执行文件
                    python_exe = os.path.join(base_path, 'python.exe')
                    if os.path.isfile(python_exe):
                        python_paths.append(python_exe)
                        self.log_message(f"✓ 从{env_var}找到Python: {python_exe}\n", "success")
        
        # 2. 检查PATH环境变量中的Python
        # 获取PATH环境变量并按路径分隔符分割
        path_env = os.environ.get('PATH', '')
        paths = path_env.split(os.pathsep)
        
        # 常见的Python可执行文件名（包括版本特定的名称）
        python_names = ['python.exe', 'python3.exe', 'python39.exe', 'python310.exe', 'python311.exe', 'python312.exe']
        
        self.log_message("🔍 检查PATH环境变量中的Python...\n", "info")
        # 遍历PATH中的每个目录
        for path in paths:
            # 检查每个可能的Python可执行文件名
            for name in python_names:
                full_path = os.path.join(path, name)
                if os.path.isfile(full_path):
                    if full_path not in python_paths:  # 避免重复添加
                        python_paths.append(full_path)
                        self.log_message(f"✓ 从PATH找到Python: {full_path}\n", "success")
        
        # 3. 检查常见的Python安装目录
        # 定义常见的Python安装路径（Windows平台）
        common_paths = [
            os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Python'),  # 用户本地应用数据目录
            os.path.join(os.environ.get('PROGRAMFILES', ''), 'Python'),              # 程序文件目录（64位）
            os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Python')         # 程序文件目录（32位）
        ]
        
        self.log_message("🔍 检查常见Python安装目录...\n", "info")
        # 遍历每个常见安装路径
        for base_path in common_paths:
            if os.path.exists(base_path):
                # 检查该目录下的所有子目录（通常是Python版本目录）
                for item in os.listdir(base_path):
                    item_path = os.path.join(base_path, item)
                    if os.path.isdir(item_path):
                        python_exe = os.path.join(item_path, 'python.exe')
                        if os.path.isfile(python_exe) and python_exe not in python_paths:
                            python_paths.append(python_exe)
                            self.log_message(f"✓ 从安装目录找到Python: {python_exe}\n", "success")
        
        # 3.1 检查Windows注册表中的Python安装
        self.log_message("🔍 检查Windows注册表中的Python安装...\n", "info")
        registry_paths = self._scan_windows_registry()
        for python_exe in registry_paths:
            if os.path.isfile(python_exe) and python_exe not in python_paths:
                python_paths.append(python_exe)
                self.log_message(f"✓ 从注册表找到Python: {python_exe}\n", "success")
        
        # 4. 根据已找到的Python路径，检测相关的虚拟环境
        self.log_message("🔍 基于已检测到的Python路径搜索虚拟环境...\n", "info")
        self._detect_virtual_environments_from_python_paths(python_paths)
        
        # 5. 检测独立的虚拟环境（不依赖于已找到的Python）
        self.log_message("🔍 检测base环境...\n", "info")
        self._detect_standalone_virtual_environments(python_paths)
        
        # 去重处理：移除重复的Python路径
        python_paths = list(set(python_paths))
        
        # 记录性能统计
        self._log_detection_performance(start_time, "Python环境检测")
        
        # 更新检测时间戳
        self._update_detection_timestamp()
        
        return python_paths
    
    def _update_detection_timestamp(self):
        """更新检测时间戳
        
        在每次完整检测后更新时间戳，用于缓存有效性检查。
        """
        import time
        timestamp_file = os.path.join(self.cache_dir, "last_detection_timestamp.txt")
        try:
            timestamp = time.time()
            with open(timestamp_file, 'w') as f:
                f.write(f"{timestamp:.6f}")
            self.log_message(f"✅ 更新检测时间戳: {timestamp:.6f}\n", "success")
        except Exception as e:
            self.log_message(f"⚠ 更新检测时间戳失败: {e}\n", "warning")
    
    def _log_detection_performance(self, start_time, detection_type):
        """记录检测性能统计
        
        Args:
            start_time (float): 检测开始时间
            detection_type (str): 检测类型描述
        """
        import time
        
        # 计算检测耗时
        elapsed_time = time.time() - start_time
        
        # 更新统计信息
        self.total_detection_count += 1
        self.detection_times.append(elapsed_time)
        
        # 记录日志
        self.log_message(f"⏱️ {detection_type}耗时: {elapsed_time:.2f}秒\n", "info")
        
        # 如果检测次数较多，计算平均耗时
        if len(self.detection_times) > 1:
            avg_time = sum(self.detection_times) / len(self.detection_times)
            self.log_message(f"📊 平均检测耗时: {avg_time:.2f}秒 (共{self.total_detection_count}次)\n", "info")
    
    def _scan_windows_registry(self):
        """扫描Windows注册表查找Python安装
        
        通过查询Windows注册表中的Python安装信息，
        获取官方Python和其他通过MSI安装的Python版本。
        
        Returns:
            list: 从注册表找到的Python可执行文件路径列表
        """
        python_paths = []
        
        try:
            import winreg
            
            # 定义要查询的注册表路径
            registry_paths = [
                r"SOFTWARE\Python\PythonCore",  # 官方Python
                r"SOFTWARE\WOW6432Node\Python\PythonCore"  # 32位Python在64位系统上
            ]
            
            # 定义要查询的根键
            root_keys = [
                (winreg.HKEY_LOCAL_MACHINE, "HKEY_LOCAL_MACHINE"),
                (winreg.HKEY_CURRENT_USER, "HKEY_CURRENT_USER")
            ]
            
            for root_key, root_name in root_keys:
                for reg_path in registry_paths:
                    try:
                        # 打开注册表键
                        with winreg.OpenKey(root_key, reg_path) as key:
                            # 枚举所有子键（Python版本）
                            i = 0
                            while True:
                                try:
                                    version = winreg.EnumKey(key, i)
                                    i += 1
                                    
                                    # 构建完整路径
                                    version_path = f"{reg_path}\\{version}\\InstallPath"
                                    
                                    try:
                                        # 获取安装路径
                                        with winreg.OpenKey(root_key, version_path) as install_key:
                                            install_path, _ = winreg.QueryValueEx(install_key, "")
                                            
                                            # 验证路径是否存在
                                            if os.path.exists(install_path):
                                                python_exe = os.path.join(install_path, "python.exe")
                                                if os.path.isfile(python_exe):
                                                    python_paths.append(python_exe)
                                                    self.log_message(f"🔍 从{root_name}注册表找到Python {version}: {python_exe}\n", "info")
                                                
                                                # 检查Scripts目录
                                                scripts_python = os.path.join(install_path, "Scripts", "python.exe")
                                                if os.path.isfile(scripts_python):
                                                    python_paths.append(scripts_python)
                                                    self.log_message(f"🔍 从{root_name}注册表找到Python Scripts {version}: {scripts_python}\n", "info")
                                                
                                    except (OSError, WindowsError):
                                        # 某些版本可能没有InstallPath键
                                        continue
                                        
                                except OSError:
                                    # 枚举完成
                                    break
                                    
                    except (OSError, WindowsError):
                        # 注册表路径不存在，跳过
                        continue
                        
        except ImportError:
            self.log_message("⚠ 无法导入winreg模块，跳过Windows注册表扫描\n", "warning")
        except Exception as e:
            self.log_message(f"⚠ 扫描Windows注册表时出错: {e}\n", "warning")
        
        # 去重并返回
        return list(set(python_paths))
    
    def _detect_virtual_environments_from_python_paths(self, python_paths):
        """基于已检测到的Python路径搜索相关虚拟环境
        
        该方法通过分析已找到的Python路径，识别它们所属的环境管理器（如Conda、
        Miniconda、Anaconda等），然后搜索该环境管理器中的其他虚拟环境。
        
        Args:
            python_paths (list): 已检测到的Python路径列表，
                               该列表会被修改以添加新发现的虚拟环境
        """
        import glob
        
        # 记录开始时间用于性能监控
        start_time = time.time()
        
        # 检测与已发现Python相关的虚拟环境
        virtual_env_paths = []
        
        # 添加调试信息
        self.log_message("🔍 基于已检测Python路径搜索相关虚拟环境...\n", "info")
        
        # 检查每个Python路径是否属于环境管理器，如果是，则搜索该环境管理器中的其他环境
        for python_path in python_paths:
            python_dir = os.path.dirname(python_path)  # 获取Python可执行文件所在目录
            parent_dir = os.path.dirname(python_dir)  # 获取父目录
            parent_name = os.path.basename(parent_dir).lower()  # 获取父目录名称
            
            # 如果Python路径在envs目录下，说明是conda环境，获取环境管理器基础路径
            if parent_name == 'envs':
                manager_base = os.path.dirname(parent_dir)  # 获取环境管理器基础路径
                manager_type = 'conda'  # 默认类型为conda
                
                # 根据路径判断具体的环境管理器类型
                if 'miniforge3' in manager_base.lower():
                    manager_type = 'miniforge'
                elif 'anaconda3' in manager_base.lower():
                    manager_type = 'anaconda'
                elif 'miniconda3' in manager_base.lower():
                    manager_type = 'miniconda'
                elif 'mambaforge' in manager_base.lower():
                    manager_type = 'mamba'
                
                self.log_message(f"🔍 发现{manager_type}环境管理器: {manager_base}\n", "info")
                
                # 检查该环境管理器中的所有环境
                envs_dir = os.path.join(manager_base, 'envs')  # 环境目录
                if os.path.exists(envs_dir):
                    # 遍历envs目录下的所有环境
                    for env_name in os.listdir(envs_dir):
                        env_path = os.path.join(envs_dir, env_name)
                        if os.path.isdir(env_path):
                            env_python = os.path.join(env_path, 'python.exe')
                            if os.path.isfile(env_python) and env_python not in python_paths:
                                virtual_env_paths.append(env_python)
                                self.log_message(f"🔍 在{manager_type}环境找到相关虚拟环境: {env_python}\n", "info")
                
                # 检查基础环境（base环境）
                base_python = os.path.join(manager_base, 'python.exe')
                if os.path.isfile(base_python) and base_python not in python_paths:
                    virtual_env_paths.append(base_python)
                    self.log_message(f"🔍 在{manager_type}基础环境找到Python: {base_python}\n", "info")
        
        # 验证并添加相关虚拟环境
        valid_count = 0
        for venv_python in virtual_env_paths:
            if self._is_valid_virtual_environment(venv_python):
                python_paths.append(venv_python)  # 将验证通过的虚拟环境添加到主列表
                valid_count += 1
                self.log_message(f"✓ 添加相关虚拟环境: {venv_python}\n", "info")
            else:
                self.log_message(f"⚠ 相关虚拟环境验证失败: {venv_python}\n", "warning")
        
        self.log_message(f"🔍 基于Python路径搜索完成，共添加 {valid_count} 个相关虚拟环境\n", "info")
        
        # 记录性能统计
        self._log_detection_performance(start_time, "基于Python路径的虚拟环境检测")

    def _detect_standalone_virtual_environments(self, python_paths):
        """检测独立的虚拟环境
        
        该方法检测不依赖于已发现Python路径的独立虚拟环境，包括：
        1. 当前工作目录及其子目录中的虚拟环境
        2. 用户主目录及其子目录中的虚拟环境  
        3. Python环境管理器（conda、miniconda、miniforge3等）中的环境
        
        Args:
            python_paths (list): 用于存储检测到的Python路径的列表，
                               该列表会被修改以添加新发现的虚拟环境
        """
        import glob
        
        # 记录开始时间用于性能监控
        start_time = time.time()
        
        # 检测独立的虚拟环境（不依赖于已发现的Python路径）
        virtual_env_paths = []
        
        # 添加调试信息
        self.log_message("🔍 开始检测base环境...\n", "info")
        
        # 仅支持Windows平台下的虚拟环境检测
        
        # 1. 检查当前工作目录及其子目录中的虚拟环境
        current_dir = os.getcwd()  # 获取当前工作目录
        venv_names = ['venv', 'env', '.venv', '.env', 'virtualenv']  # 常见的虚拟环境目录名称
        
        self.log_message(f"🔍 搜索当前工作目录: {current_dir}\n", "info")
        
        # 递归搜索当前目录及其子目录
        for root, dirs, files in os.walk(current_dir):
            # 限制搜索深度，避免过深搜索影响性能
            if root.count(os.sep) - current_dir.count(os.sep) > 3:
                continue
                
            # 检查每个子目录是否是虚拟环境目录
            for dir_name in dirs:
                if dir_name.lower() in [v.lower() for v in venv_names]:
                    venv_path = os.path.join(root, dir_name)
                    python_exe = os.path.join(venv_path, 'Scripts', 'python.exe')  # Windows风格的Python路径
                    if os.path.isfile(python_exe) and python_exe not in python_paths:
                        virtual_env_paths.append(python_exe)
                        self.log_message(f"🔍 在当前目录找到候选虚拟环境: {python_exe}\n", "info")
                            
        # 2. 检查用户目录下的虚拟环境
        user_dir = os.path.expanduser('~')  # 获取用户主目录
        self.log_message(f"🔍 搜索用户目录: {user_dir}\n", "info")
        
        # 递归搜索用户目录及其子目录
        for root, dirs, files in os.walk(user_dir):
            # 限制搜索深度，避免搜索过深影响性能（用户目录通常较大）
            if root.count(os.sep) - user_dir.count(os.sep) > 2:
                continue
                
            # 检查每个子目录是否是虚拟环境目录
            for dir_name in dirs:
                if dir_name.lower() in [v.lower() for v in venv_names]:
                    venv_path = os.path.join(root, dir_name)
                    python_exe = os.path.join(venv_path, 'Scripts', 'python.exe')  # Windows风格的Python路径
                    if os.path.isfile(python_exe) and python_exe not in python_paths:
                        virtual_env_paths.append(python_exe)
                        self.log_message(f"🔍 在用户目录找到候选虚拟环境: {python_exe}\n", "info")
                            
        # 3. 检查Python环境管理器（conda、miniconda、miniforge3等）
        env_managers = []  # 存储找到的环境管理器信息
            
        # 首先从环境变量获取Python环境管理器路径
        env_vars_to_check = [
            ('CONDA_PREFIX', 'conda'),      # Conda环境前缀（指向具体环境）
            ('CONDA_HOME', 'conda'),        # Conda主目录
            ('MINICONDA_HOME', 'miniconda'), # Miniconda主目录
            ('MINIFORGE_HOME', 'miniforge'), # Miniforge主目录
            ('MAMBA_HOME', 'mamba')         # Mamba主目录
        ]
        
        # 遍历环境变量，查找已安装的环境管理器
        for env_var, manager_type in env_vars_to_check:
            if env_var in os.environ:
                if env_var == 'CONDA_PREFIX':
                    # CONDA_PREFIX指向的是具体环境，需要获取基础目录
                    conda_prefix = os.environ[env_var]
                    # 检查是否在envs目录下，如果是，需要向上两级目录获取基础目录
                    if 'envs' in conda_prefix:
                        # 如果在envs目录下，说明是conda虚拟环境，需要向上两级获取conda安装根目录
                        base_path = os.path.dirname(os.path.dirname(conda_prefix))  # 从 envs/env_name 向上两级
                    else:
                        # 否则直接向上一级获取基础目录（可能是base环境）
                        base_path = os.path.dirname(conda_prefix)
                    
                    # 如果基础目录不包含miniforge3或anaconda3等，尝试向上查找
                    if not any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                        # 尝试在当前目录下查找这些目录
                        parent_dir = base_path
                        for _ in range(3):  # 最多向上查找3级目录
                            for name in ['miniforge3', 'anaconda3', 'miniconda3']:  # 常见的conda发行版目录名
                                test_path = os.path.join(parent_dir, name)  # 构建测试路径
                                if os.path.exists(test_path):  # 检查路径是否存在
                                    base_path = test_path  # 更新为基础路径
                                    break  # 找到后跳出内层循环
                            if any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                                break  # 找到有效的conda安装目录后跳出外层循环
                            parent_dir = os.path.dirname(parent_dir)  # 继续向上查找
                else:
                    # 对于其他环境变量，直接使用环境变量指向的路径作为基础路径
                    base_path = os.environ[env_var]  # 直接使用环境变量指向的路径
                
                # 将找到的环境管理器信息添加到列表
                env_managers.append({
                    'type': manager_type,
                    'path': base_path,
                    'source': f'环境变量 {env_var}'
                })
                self.log_message(f"🔍 从{env_var}找到{manager_type}路径: {base_path}\n", "info")
            
        # 如果没有从环境变量找到，搜索常见的安装路径
        if not env_managers:
            # 常见的Python环境管理器安装路径（覆盖多种安装位置）
            common_manager_paths = [
                # Miniconda3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniconda3'), 'miniconda'),
                # Miniconda3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniconda3'), 'miniconda'),
                # Miniconda3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniconda3'), 'miniconda'),
                
                # Anaconda3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Anaconda3'), 'anaconda'),
                # Anaconda3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Anaconda3'), 'anaconda'),
                # Anaconda3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Anaconda3'), 'anaconda'),
                
                # Miniforge3 - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniforge3'), 'miniforge'),
                # Miniforge3 - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniforge3'), 'miniforge'),
                # Miniforge3 - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniforge3'), 'miniforge'),
                
                # Mambaforge - LocalAppData/Programs目录（用户级安装）
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Mambaforge'), 'mamba'),
                # Mambaforge - ProgramFiles目录（系统级安装）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Mambaforge'), 'mamba'),
                # Mambaforge - ProgramFiles(x86)目录（32位系统）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Mambaforge'), 'mamba'),
                
                # 用户主目录下的安装（手动安装到用户目录）
                (os.path.join(os.path.expanduser('~'), 'miniconda3'), 'miniconda'),
                (os.path.join(os.path.expanduser('~'), 'anaconda3'), 'anaconda'),
                (os.path.join(os.path.expanduser('~'), 'miniforge3'), 'miniforge'),
                (os.path.join(os.path.expanduser('~'), 'mambaforge'), 'mamba'),
                
                # 常见自定义安装路径（特定软件安装目录）
                ('F:\\itsoft\\miniforge3', 'miniforge'),
                ('C:\\itsoft\\miniforge3', 'miniforge'),
                ('D:\\itsoft\\miniforge3', 'miniforge'),
                ('E:\\itsoft\\miniforge3', 'miniforge')
            ]
                
            # 遍历所有常见安装路径，查找存在的环境管理器
            self.log_message(f"🔍 搜索Python环境管理器安装路径...\n", "info")
            for manager_path, manager_type in common_manager_paths:
                if os.path.exists(manager_path):
                    env_managers.append({
                        'type': manager_type,
                        'path': manager_path,
                        'source': '常见安装路径'
                    })
                    self.log_message(f"🔍 找到{manager_type}安装路径: {manager_path}\n", "info")
            
            # 如果仍未找到任何环境管理器，输出提示信息
            if not env_managers:
                self.log_message(f"⚠ 未找到Python环境管理器安装路径\n", "info")
            
        # 检查每个环境管理器中的环境
        for manager in env_managers:
            manager_path = manager['path']  # 环境管理器基础路径
            manager_type = manager['type']  # 环境管理器类型
            
            if os.path.exists(manager_path):
                # 检查envs目录（conda系列环境管理器的虚拟环境存储目录）
                envs_dir = os.path.join(manager_path, 'envs')
                self.log_message(f"🔍 检查{manager_type}环境目录: {envs_dir}\n", "info")
                
                if os.path.exists(envs_dir):
                    # 遍历envs目录下的所有虚拟环境
                    for env_name in os.listdir(envs_dir):
                        env_path = os.path.join(envs_dir, env_name)
                        if os.path.isdir(env_path):
                            python_exe = os.path.join(env_path, 'python.exe')
                            if os.path.isfile(python_exe) and python_exe not in python_paths:
                                virtual_env_paths.append(python_exe)
                                self.log_message(f"🔍 在{manager_type}环境找到候选虚拟环境: {python_exe}\n", "info")
                else:
                    self.log_message(f"⚠ {manager_type}环境目录不存在: {envs_dir}\n", "info")
                
                # 检查基础环境（base环境）- 环境管理器的根Python环境
                base_python = os.path.join(manager_path, 'python.exe')
                if os.path.isfile(base_python) and base_python not in python_paths:
                    virtual_env_paths.append(base_python)
                    self.log_message(f"🔍 在{manager_type}基础环境找到Python: {base_python}\n", "info")
            else:
                self.log_message(f"⚠ {manager_type}基础目录不存在: {manager_path}\n", "info")
            
        # 添加调试信息
        self.log_message(f"🔍 检测到 {len(virtual_env_paths)} 个候选独立虚拟环境\n", "info")
        
        # 验证虚拟环境并添加到结果列表
        valid_count = 0
        for venv_python in virtual_env_paths:
            if self._is_valid_virtual_environment(venv_python):
                python_paths.append(venv_python)  # 将验证通过的虚拟环境添加到主列表
                valid_count += 1
                self.log_message(f"✓ 发现独立虚拟环境: {venv_python}\n", "info")
            else:
                self.log_message(f"⚠ 独立虚拟环境验证失败: {venv_python}\n", "warning")
        
        # 添加调试信息
        self.log_message(f"🔍 独立虚拟环境检测完成，共找到 {valid_count} 个有效虚拟环境\n", "info")
        
        # 记录性能统计
        self._log_detection_performance(start_time, "独立虚拟环境检测")
        
        # 检查环境变量中的环境管理器路径
        env_vars = [
            ('CONDA_PREFIX', 'conda'),
            ('MINICONDA_PREFIX', 'miniconda'),
            ('ANACONDA_PREFIX', 'anaconda')
        ]
        
        env_managers = []  # 环境管理器列表
        for env_var, manager_type in env_vars:
            if env_var in os.environ:
                base_path = os.path.dirname(os.environ[env_var])
                
                # 向上查找环境管理器根目录
                parent_dir = base_path
                for _ in range(3):  # 最多向上查找3级
                    for name in ['miniforge3', 'anaconda3', 'miniconda3']:
                        test_path = os.path.join(parent_dir, name)
                        if os.path.exists(test_path):
                            base_path = test_path
                            break
                    if any(name in base_path.lower() for name in ['miniforge3', 'anaconda3', 'miniconda3']):
                        break
                    parent_dir = os.path.dirname(parent_dir)
            else:
                # 环境变量不存在，跳过
                continue
            
            env_managers.append({
                'type': manager_type,           # 环境管理器类型（conda、miniconda等）
                'path': base_path,             # 环境管理器安装路径
                'source': f'环境变量 {env_var}' # 来源说明（从哪个环境变量获取的）
            })
            self.log_message(f"🔍 从{env_var}找到{manager_type}路径: {base_path}\n", "info")  # 记录找到的环境管理器信息
        
        # 如果没有从环境变量找到，搜索常见的安装路径
        if not env_managers:  # 检查是否已经通过环境变量找到了环境管理器
            # 常见的Python环境管理器安装路径
            common_manager_paths = [
                # Miniconda3 - 不同安装位置的路径
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniconda3'), 'miniconda'),  # 用户级安装（LocalAppData）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniconda3'), 'miniconda'),               # 系统级安装（ProgramFiles）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniconda3'), 'miniconda'),         # 32位系统安装
                
                # Anaconda3 - 不同安装位置的路径
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Anaconda3'), 'anaconda'),     # 用户级安装（LocalAppData）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Anaconda3'), 'anaconda'),                # 系统级安装（ProgramFiles）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Anaconda3'), 'anaconda'),          # 32位系统安装
                
                # Miniforge3 - 不同安装位置的路径
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Miniforge3'), 'miniforge'),   # 用户级安装（LocalAppData）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Miniforge3'), 'miniforge'),              # 系统级安装（ProgramFiles）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Miniforge3'), 'miniforge'),        # 32位系统安装
                
                # Mambaforge - 不同安装位置的路径
                (os.path.join(os.environ.get('LOCALAPPDATA', ''), 'Programs', 'Mambaforge'), 'mamba'),      # 用户级安装（LocalAppData）
                (os.path.join(os.environ.get('PROGRAMFILES', ''), 'Mambaforge'), 'mamba'),                 # 系统级安装（ProgramFiles）
                (os.path.join(os.environ.get('PROGRAMFILES(X86)', ''), 'Mambaforge'), 'mamba'),           # 32位系统安装
                
                # 用户主目录下的安装 - 用户自定义安装位置
                (os.path.join(os.path.expanduser('~'), 'miniconda3'), 'miniconda'),  # 用户主目录下的Miniconda3
                (os.path.join(os.path.expanduser('~'), 'anaconda3'), 'anaconda'),     # 用户主目录下的Anaconda3
                (os.path.join(os.path.expanduser('~'), 'miniforge3'), 'miniforge'),   # 用户主目录下的Miniforge3
                (os.path.join(os.path.expanduser('~'), 'mambaforge'), 'mamba'),       # 用户主目录下的Mambaforge
                
                # 常见自定义安装路径 - itsoft目录下的Miniforge3
                ('F:\\itsoft\\miniforge3', 'miniforge'),  # F盘itsoft目录下的Miniforge3
                ('C:\\itsoft\\miniforge3', 'miniforge'),  # C盘itsoft目录下的Miniforge3
                ('D:\\itsoft\\miniforge3', 'miniforge'),  # D盘itsoft目录下的Miniforge3
                ('E:\\itsoft\\miniforge3', 'miniforge')   # E盘itsoft目录下的Miniforge3
            ]
                
            # 遍历所有预定义的环境管理器安装路径
            self.log_message(f"🔍 搜索Python环境管理器安装路径...\n", "info")
            for manager_path, manager_type in common_manager_paths:
                if os.path.exists(manager_path):  # 检查路径是否存在
                    env_managers.append({
                        'type': manager_type,           # 环境管理器类型
                        'path': manager_path,           # 环境管理器安装路径
                        'source': '常见安装路径'       # 来源说明
                    })
                    self.log_message(f"🔍 找到{manager_type}安装路径: {manager_path}\n", "info")  # 记录找到的环境管理器
            
            # 如果没有找到任何环境管理器，记录警告信息
            if not env_managers:
                self.log_message(f"⚠ 未找到Python环境管理器安装路径\n", "info")
            
        # 检查每个环境管理器中的环境
        for manager in env_managers:
            manager_path = manager['path']    # 环境管理器安装路径
            manager_type = manager['type']    # 环境管理器类型
            
            if os.path.exists(manager_path):  # 检查环境管理器基础目录是否存在
                # 检查envs目录（conda系列环境管理器的环境存储目录）
                envs_dir = os.path.join(manager_path, 'envs')  # 构建envs目录路径
                self.log_message(f"🔍 检查{manager_type}环境目录: {envs_dir}\n", "info")
                
                if os.path.exists(envs_dir):  # 检查envs目录是否存在
                    # 遍历envs目录中的所有子目录（每个子目录代表一个conda环境）
                    for env_name in os.listdir(envs_dir):
                        env_path = os.path.join(envs_dir, env_name)  # 构建环境路径
                        if os.path.isdir(env_path):  # 确保是目录
                            python_exe = os.path.join(env_path, 'python.exe')  # 构建Python可执行文件路径
                            if os.path.isfile(python_exe):  # 验证Python可执行文件是否存在
                                virtual_env_paths.append(python_exe)  # 添加到候选虚拟环境列表
                                self.log_message(f"🔍 在{manager_type}环境找到候选虚拟环境: {python_exe}\n", "info")
                else:
                    self.log_message(f"⚠ {manager_type}环境目录不存在: {envs_dir}\n", "info")
                
                # 检查基础环境（base环境）- conda系列环境管理器的基础Python环境
                base_python = os.path.join(manager_path, 'python.exe')  # 构建基础环境Python可执行文件路径
                if os.path.isfile(base_python):  # 验证基础环境Python可执行文件是否存在
                    virtual_env_paths.append(base_python)  # 添加到候选虚拟环境列表
                    self.log_message(f"🔍 在{manager_type}基础环境找到Python: {base_python}\n", "info")
            else:
                self.log_message(f"⚠ {manager_type}基础目录不存在: {manager_path}\n", "info")
            

                                

        
        # 添加调试信息 - 统计候选虚拟环境数量
        self.log_message(f"🔍 检测到 {len(virtual_env_paths)} 个候选虚拟环境\n", "info")
        
        # 验证虚拟环境并添加到结果列表
        valid_count = 0  # 有效虚拟环境计数器
        for venv_python in virtual_env_paths:  # 遍历所有候选虚拟环境
            if self._is_valid_virtual_environment(venv_python):  # 验证虚拟环境有效性
                python_paths.append(venv_python)  # 将有效虚拟环境添加到结果列表
                valid_count += 1  # 增加有效计数器
                self.log_message(f"✓ 发现虚拟环境: {venv_python}\n", "info")
            else:
                self.log_message(f"⚠ 虚拟环境验证失败: {venv_python}\n", "warning")
        
        # 添加调试信息 - 总结检测结果
        self.log_message(f"🔍 虚拟环境检测完成，共找到 {valid_count} 个有效虚拟环境\n", "info")
    
    def _verify_python_interpreter(self, python_path):
        """验证Python解释器是否可以正常运行
        
        Args:
            python_path (str): Python解释器路径
            
        Returns:
            bool: Python解释器是否可用
        """
        try:
            # 首先验证文件是否存在且可执行
            if not os.path.isfile(python_path):
                self.log_message(f"⚠ Python解释器文件不存在: {python_path}\n", "warning")
                return False
            
            # 设置基本环境变量
            temp_env = os.environ.copy()
            python_dir = os.path.dirname(python_path)
            
            # 确定是否为虚拟环境并设置相应的环境变量
            if self._is_valid_virtual_environment(python_path):
                # 获取虚拟环境根目录
                venv_root = self._get_virtual_env_root(python_path) or python_dir
                
                # 为虚拟环境设置更完整的环境变量
                if platform.system() == "Windows":
                    scripts_dir = os.path.join(python_dir, 'Scripts')
                    # 确保Scripts目录存在
                    if not os.path.exists(scripts_dir) and os.path.basename(python_dir).lower() != 'scripts':
                        scripts_dir = os.path.join(venv_root, 'Scripts')
                else:
                    scripts_dir = os.path.join(venv_root, 'bin')
                
                # 对于conda环境，设置CONDA_PREFIX
                if 'conda' in python_path.lower() or 'envs' in python_path.lower():
                    temp_env['CONDA_PREFIX'] = venv_root
                    # 设置conda相关的环境变量
                    conda_root = os.path.dirname(venv_root) if 'envs' in venv_root else venv_root
                    conda_bin = os.path.join(conda_root, 'condabin')
                    if os.path.exists(conda_bin):
                        temp_env['PATH'] = f"{conda_bin}{os.pathsep}{temp_env['PATH']}"
                
                # 对于标准虚拟环境，设置VIRTUAL_ENV
                else:
                    temp_env['VIRTUAL_ENV'] = venv_root
            
            # 确保Python目录在PATH中（对于非系统Python尤为重要）
            if python_dir not in temp_env["PATH"]:
                temp_env["PATH"] = f"{python_dir}{os.pathsep}{temp_env['PATH']}"
            
            # 确保Scripts/bin目录在PATH中
            if os.path.exists(scripts_dir) and scripts_dir not in temp_env["PATH"]:
                temp_env["PATH"] = f"{scripts_dir}{os.pathsep}{temp_env['PATH']}"
            
            # 尝试运行Python解释器获取版本信息
            self.log_message(f"🔍 尝试运行Python解释器: {python_path}\n", "info")
            
            # 使用完整路径和增强的环境变量执行Python
            result = subprocess.run(
                [python_path, '--version'], 
                stdout=subprocess.PIPE, 
                stderr=subprocess.PIPE, 
                text=True,
                timeout=10,  # 增加超时时间以处理可能较慢的环境
                env=temp_env,
                shell=False  # 直接执行，不使用shell
            )
            
            # Python的版本信息可能输出到stdout或stderr，所以检查returncode
            success = result.returncode == 0
            if success:
                version_info = result.stdout.strip() or result.stderr.strip()
                self.log_message(f"✓ Python解释器验证成功: {version_info}\n", "success")
                return True
            else:
                # 如果第一次失败，尝试使用shell执行（对于某些特殊情况可能有帮助）
                self.log_message(f"⚠ 直接执行失败，尝试使用shell执行\n", "warning")
                result = subprocess.run(
                    f'"{python_path}" --version', 
                    stdout=subprocess.PIPE, 
                    stderr=subprocess.PIPE, 
                    text=True,
                    timeout=10,
                    env=temp_env,
                    shell=True  # 使用shell执行
                )
                
                success = result.returncode == 0
                if success:
                    version_info = result.stdout.strip() or result.stderr.strip()
                    self.log_message(f"✓ 使用shell执行Python解释器成功: {version_info}\n", "success")
                else:
                    error_output = result.stderr.strip() or result.stdout.strip()
                    self.log_message(f"⚠ Python解释器执行失败: {error_output}\n", "warning")
                
                return success
                
        except subprocess.TimeoutExpired:
            self.log_message(f"⚠ Python解释器执行超时: {python_path}\n", "warning")
            return False
        except FileNotFoundError:
            self.log_message(f"⚠ 找不到Python解释器文件: {python_path}\n", "error")
            return False
        except PermissionError:
            self.log_message(f"⚠ 无权限执行Python解释器: {python_path}\n", "error")
            return False
        except Exception as e:
            self.log_message(f"⚠ 验证Python解释器时出错: {str(e)}\n", "warning")
            # 即使发生异常，也尝试返回True，因为文件存在且可能在实际使用时能正常工作
            # 这是为了更好地支持非标准环境
            return os.path.isfile(python_path)
    
    def _is_valid_virtual_environment(self, python_path):
        """验证是否为有效的虚拟环境
        
        Args:
            python_path (str): Python解释器路径
            
        Returns:
            bool: 是否为有效的虚拟环境
        """
        try:
            # 添加调试信息 - 记录当前验证的Python路径
            self.log_message(f"🔍 验证虚拟环境: {python_path}\n", "info")
            
            # 首先检查Python文件是否存在 - 基本验证
            if not os.path.isfile(python_path):
                self.log_message(f"⚠ Python文件不存在: {python_path}\n", "warning")
                return False
            
            # 检查是否存在虚拟环境标识文件 - 确定虚拟环境根目录
            venv_dir = os.path.dirname(python_path)  # 获取Python文件所在目录
            if platform.system() == "Windows":  # Windows系统特殊处理
                # Windows系统下，python.exe可能在不同的位置
                # 1. 标准虚拟环境: venv\Scripts\python.exe
                # 2. conda环境: miniforge3\envs\env_name\python.exe
                # 3. conda基础环境: miniforge3\python.exe
                parent_dir = os.path.dirname(venv_dir)  # 获取父目录
                parent_name = os.path.basename(parent_dir).lower()  # 获取父目录名称（小写）
                
                # 如果父目录是'scripts'，则是标准虚拟环境
                if parent_name == 'scripts':
                    venv_dir = parent_dir  # venv根目录（Scripts的父目录）
                # 如果父目录是'envs'，则是conda环境
                elif parent_name == 'envs':
                    venv_dir = venv_dir  # 环境目录本身就是根目录（如miniforge3\envs\env_name）
                # 否则检查是否是conda基础环境（如miniforge3、anaconda3等）
                else:
                    # 检查当前目录是否包含conda相关文件
                    if (os.path.isfile(os.path.join(venv_dir, 'conda.exe')) or 
                        os.path.isdir(os.path.join(venv_dir, 'condabin')) or
                        os.path.isdir(os.path.join(venv_dir, 'Library'))):
                        # 这是conda基础环境，venv_dir就是根目录
                        pass
                    else:
                        # 其他情况，向上一级
                        venv_dir = parent_dir  # 向上一级查找虚拟环境根目录
            else:
                venv_dir = os.path.dirname(venv_dir)  # 从bin目录回到venv根目录（Linux/macOS）
            
            self.log_message(f"🔍 虚拟环境根目录: {venv_dir}\n", "info")
            
            # 检查pyvenv.cfg文件（标准虚拟环境标识）
            pyvenv_cfg = os.path.join(venv_dir, 'pyvenv.cfg')  # 构建pyvenv.cfg文件路径
            if os.path.isfile(pyvenv_cfg):  # 检查pyvenv.cfg文件是否存在
                self.log_message(f"✓ 找到pyvenv.cfg文件\n", "info")
                return True  # 找到标准虚拟环境标识，验证通过
            else:
                self.log_message(f"⚠ 未找到pyvenv.cfg文件\n", "info")
                
            # 检查conda环境的标识 - conda-meta目录
            conda_meta = os.path.join(venv_dir, 'conda-meta')  # 构建conda-meta目录路径
            if os.path.isdir(conda_meta):  # 检查conda-meta目录是否存在
                self.log_message(f"✓ 找到conda-meta目录: {conda_meta}\n", "info")
                return True  # 找到conda环境标识，验证通过
            else:
                self.log_message(f"⚠ 未找到conda-meta目录: {conda_meta}\n", "info")
                
            # 检查是否包含虚拟环境特有的目录结构 - site-packages目录验证
            has_site_packages = False  # site-packages目录存在标志
            if platform.system() == "Windows":  # Windows系统特殊处理
                # Windows系统下，检查不同类型的虚拟环境
                parent_dir = os.path.dirname(venv_dir)  # 获取虚拟环境目录的父目录
                parent_name = os.path.basename(parent_dir).lower()  # 获取父目录名称（小写）
                
                # 如果是conda环境（父目录是envs）
                if parent_name == 'envs':
                    # conda环境的site-packages路径: env_name\Lib\site-packages
                    site_packages = os.path.join(venv_dir, 'Lib', 'site-packages')  # conda环境site-packages路径
                else:
                    # 标准虚拟环境或conda基础环境
                    site_packages = os.path.join(venv_dir, 'Lib', 'site-packages')  # 标准虚拟环境site-packages路径
            else:
                # Linux/macOS系统下的site-packages路径（使用通配符匹配Python版本）
                site_packages = os.path.join(venv_dir, 'lib', 'python*', 'site-packages')
                
            self.log_message(f"🔍 检查site-packages目录: {site_packages}\n", "info")
                
            # 使用glob匹配可能的site-packages目录（处理通配符路径）
            if '*' in site_packages:  # 检查路径是否包含通配符
                matches = glob.glob(site_packages)  # 使用glob匹配所有可能的路径
                if matches:  # 如果找到匹配的路径
                    has_site_packages = True  # 设置site-packages存在标志
                    self.log_message(f"✓ 找到site-packages目录: {matches[0]}\n", "info")
                else:
                    self.log_message(f"⚠ 未找到site-packages目录\n", "info")
            else:  # 处理不包含通配符的路径
                has_site_packages = os.path.isdir(site_packages)  # 直接检查目录是否存在
                if has_site_packages:  # 如果目录存在
                    self.log_message(f"✓ 找到site-packages目录\n", "info")
                else:
                    self.log_message(f"⚠ 未找到site-packages目录\n", "info")
            
            # 检查是否有pip等虚拟环境特有的工具 - 进一步验证虚拟环境完整性
            if platform.system() == "Windows":  # Windows系统特殊处理
                # Windows系统下，检查不同类型的虚拟环境
                parent_dir = os.path.dirname(venv_dir)  # 获取虚拟环境目录的父目录
                parent_name = os.path.basename(parent_dir).lower()  # 获取父目录名称（小写）
                
                # 如果是conda环境（父目录是envs），检查Scripts目录
                if parent_name == 'envs':
                    scripts_dir = os.path.join(venv_dir, 'Scripts')  # conda环境的Scripts目录
                    pip_path = os.path.join(scripts_dir, 'pip.exe')  # conda环境的pip可执行文件路径
                    activate_path = os.path.join(scripts_dir, 'activate.bat')  # conda环境的激活脚本路径
                else:
                    # 标准虚拟环境或conda基础环境
                    scripts_dir = os.path.join(venv_dir, 'Scripts')  # 标准虚拟环境的Scripts目录
                    pip_path = os.path.join(scripts_dir, 'pip.exe')  # 标准虚拟环境的pip可执行文件路径
                    activate_path = os.path.join(scripts_dir, 'activate.bat')  # 标准虚拟环境的激活脚本路径
            else:
                # Linux/macOS系统下的pip和activate路径
                pip_path = os.path.join(venv_dir, 'bin', 'pip')  # Linux/macOS的pip可执行文件路径
                activate_path = os.path.join(venv_dir, 'bin', 'activate')  # Linux/macOS的激活脚本路径
                
            # 验证pip和activate文件是否存在
            has_pip = os.path.isfile(pip_path)  # 检查pip可执行文件是否存在
            has_activate = os.path.isfile(activate_path)  # 检查激活脚本是否存在
            
            self.log_message(f"🔍 pip文件存在: {has_pip}, activate文件存在: {has_activate}\n", "info")
            
            # 对于conda基础环境，放宽验证条件 - conda基础环境可能缺少某些标准文件
            # 检查是否是conda基础环境（包含conda.exe、condabin、Library等conda特有文件）
            is_conda_base = (
                os.path.isfile(os.path.join(venv_dir, 'conda.exe')) or     # 检查conda可执行文件
                os.path.isdir(os.path.join(venv_dir, 'condabin')) or      # 检查condabin目录
                os.path.isdir(os.path.join(venv_dir, 'Library'))         # 检查Library目录（Windows特有）
            )
            
            if is_conda_base:  # 如果是conda基础环境
                self.log_message(f"✓ 检测到conda基础环境，放宽验证条件\n", "info")
                # conda基础环境只要有Python可执行文件就认为是有效的
                result = True
            else:  # 其他类型的虚拟环境
                # 其他虚拟环境，需要有site-packages目录或者有pip/activate文件
                result = has_site_packages or has_pip or has_activate
            
            # 根据验证结果记录相应的日志信息
            if result:  # 如果验证通过
                self.log_message(f"✓ 虚拟环境验证通过\n", "info")
            else:  # 如果验证失败
                self.log_message(f"⚠ 虚拟环境验证失败: site_packages={has_site_packages}, pip={has_pip}, activate={has_activate}\n", "warning")
            
            return result  # 返回验证结果
            
        except Exception as e:  # 捕获所有异常
            self.log_message(f"✗ 虚拟环境验证异常: {str(e)}\n", "error")
            return False  # 发生异常时返回False
    
    def _get_virtual_env_root(self, python_path):
        """获取虚拟环境的根目录
        
        Args:
            python_path (str): Python解释器路径
            
        Returns:
            str: 虚拟环境根目录路径，如果不是虚拟环境则返回None
        """
        try:
            venv_dir = os.path.dirname(python_path)
            
            # 根据操作系统和路径特征确定虚拟环境根目录
            if platform.system() == "Windows":
                parent_dir = os.path.dirname(venv_dir)
                parent_name = os.path.basename(parent_dir).lower()
                
                # 标准虚拟环境: venv\Scripts\python.exe
                if parent_name == 'scripts':
                    return parent_dir
                # conda环境: miniforge3\envs\env_name\python.exe
                elif parent_name == 'envs':
                    return venv_dir
                # conda基础环境或其他环境
                else:
                    # 检查是否为conda基础环境
                    if (os.path.isfile(os.path.join(venv_dir, 'conda.exe')) or 
                        os.path.isdir(os.path.join(venv_dir, 'condabin')) or
                        os.path.isdir(os.path.join(venv_dir, 'Library'))):
                        return venv_dir
                    # 检查是否在标准虚拟环境的Scripts目录中
                    elif os.path.basename(venv_dir).lower() == 'scripts':
                        return parent_dir
                    else:
                        # 尝试查找pyvenv.cfg文件
                        for root, dirs, files in os.walk(venv_dir):
                            if 'pyvenv.cfg' in files:
                                return root
                            # 限制搜索深度
                            if len(os.path.relpath(root, venv_dir).split(os.sep)) > 2:
                                dirs[:] = []  # 清空dirs以停止进一步搜索
            else:
                # Linux/macOS: 通常在venv/bin/python路径
                if os.path.basename(venv_dir) == 'bin':
                    return os.path.dirname(venv_dir)
                
                # 检查conda环境
                if 'conda' in python_path or 'envs' in python_path:
                    path_parts = python_path.split(os.sep)
                    if 'envs' in path_parts:
                        envs_index = path_parts.index('envs')
                        if envs_index + 1 < len(path_parts):
                            return os.sep.join(path_parts[:envs_index + 2])
                
                # 尝试查找pyvenv.cfg文件
                for root, dirs, files in os.walk(venv_dir):
                    if 'pyvenv.cfg' in files:
                        return root
                    # 限制搜索深度
                    if len(os.path.relpath(root, venv_dir).split(os.sep)) > 2:
                        dirs[:] = []  # 清空dirs以停止进一步搜索
            
            # 如果无法确定，返回Python所在目录
            return os.path.dirname(python_path)
            
        except Exception as e:
            self.log_message(f"⚠ 获取虚拟环境根目录失败: {str(e)}\n", "warning")
            return os.path.dirname(python_path)
            
    def _get_conda_env_name(self, python_path):
        """获取Python解释器所属的conda环境名称
        
        通过分析Python解释器路径来确定其所属的conda环境名称。
        conda环境的典型路径结构为: /path/to/conda/envs/environment_name/bin/python
        conda base环境的典型路径结构为: /path/to/conda/python.exe
        
        Args:
            python_path (str): Python解释器的完整路径
            
        Returns:
            str: conda环境名称，如果不是conda环境或无法确定则返回None
        """
        try:
            # 分割路径为各个组成部分，便于后续分析
            # 例如: ['/path', 'to', 'conda', 'envs', 'myenv', 'bin', 'python']
            path_parts = python_path.split(os.sep)  # 按操作系统路径分隔符分割路径
            
            # 查找'envs'目录在路径中的位置索引
            # 这是识别conda环境结构的关键步骤
            envs_index = -1  # 初始化envs目录索引为-1，表示未找到
            for i, part in enumerate(path_parts):  # 遍历路径的各个部分
                if part == 'envs':  # 找到envs目录
                    envs_index = i  # 记录envs目录的索引位置
                    break
            
            # 如果找到envs目录，则为conda虚拟环境
            if envs_index != -1 and envs_index + 1 < len(path_parts):
                # 提取环境名称 - envs目录后的下一级目录名
                # 例如: 在路径'/path/to/conda/envs/myenv/bin/python'中，环境名称是'myenv'
                env_name = path_parts[envs_index + 1]  # 获取环境名称
                
                # 验证提取的环境路径确实存在，确保准确性
                # 构建到环境目录的完整路径进行验证
                env_path = os.sep.join(path_parts[:envs_index + 2])  # 到环境目录为止
                if os.path.exists(env_path):
                    return env_name
            
            # 如果未找到envs目录，检查是否为conda base环境
            # conda base环境路径通常包含'anaconda3'、'miniconda3'或'miniforge3'等目录名
            elif 'anaconda3' in path_parts or 'miniconda3' in path_parts or 'miniforge3' in path_parts:
                # 返回'base'作为base环境名称
                return 'base'
            
            # 如果以上条件都不满足，则不是conda环境
            return None
                
        except Exception as e:
            # 记录获取conda环境名称时发生的任何异常
            self.log_message(f"⚠ 获取conda环境名称失败: {str(e)}\n", "warning")
            return None
    
    def add_to_environment(self):
        """将Python路径添加到系统环境变量
        
        此方法允许用户将选定的Python解释器路径添加到系统的PATH环境变量中，
        使得可以在命令行中直接使用python命令。
        仅支持Windows平台，使用setx命令进行设置。
        """
        # 获取用户选择的Python解释器路径
        python_path = self.python_combo.currentText().strip()
        
        # 验证是否选择了Python解释器
        if not python_path:
            QMessageBox.warning(self, "警告", "请先选择Python解释器路径")
            return
        
        # 验证选择的Python解释器路径是否存在
        if not os.path.isfile(python_path):
            QMessageBox.warning(self, "警告", "指定的Python解释器路径不存在")
            return
        
        # 仅支持Windows平台，无需判断
        
        # 获取Python安装目录（去除可执行文件名）
        python_dir = os.path.dirname(python_path)
        
        # 检查该路径是否已经存在于系统PATH环境变量中
        path_env = os.environ.get('PATH', '')
        paths = path_env.split(os.pathsep)
        
        # 如果已经存在，提示用户无需重复添加
        if python_dir in paths:
            QMessageBox.information(self, "提示", "该Python路径已经在系统环境变量中")
            return
        
        # 询问用户是否要添加到系统环境变量
        # 显示确认对话框，告知用户将要执行的操作和注意事项
        reply = QMessageBox.question(
            self, 
            "确认",
            f"是否将以下路径添加到系统环境变量PATH中？\n\n{python_dir}\n\n注意：此操作需要管理员权限，并且可能需要重启程序才能生效。",
            QMessageBox.Yes | QMessageBox.No
        )
        
        # 如果用户确认添加
        if reply == QMessageBox.Yes:
            try:
                # 使用setx命令添加到系统环境变量
                import subprocess
                
                # 获取当前PATH环境变量
                current_path = os.environ.get('PATH', '')
                # 构建新的PATH环境变量，将Python目录添加到最前面
                new_path = f"{python_dir};{current_path}"
                
                # 使用setx命令设置系统环境变量
                # /M 参数表示设置系统环境变量（需要管理员权限）
                subprocess.run(['setx', 'PATH', new_path, '/M'], check=True, shell=True)
                
                # 显示成功消息
                QMessageBox.information(
                    self, 
                    "成功", 
                    f"已成功将Python路径添加到系统环境变量中。\n\n请重启程序或重新登录系统以使更改生效。"
                )
                # 记录成功日志
                self.log_message(f"✓ 已将Python路径添加到系统环境变量: {python_dir}\n", "success")
                
            except subprocess.CalledProcessError as e:
                # 处理setx命令执行失败的情况（通常是权限不足）
                QMessageBox.critical(
                    self, 
                    "失败", 
                    f"添加环境变量失败，请以管理员身份运行此程序。\n\n错误信息: {str(e)}"
                )
                # 记录错误日志
                self.log_message(f"✗ 添加环境变量失败: {str(e)}\n", "error")
            except Exception as e:
                # 处理其他可能的异常
                QMessageBox.critical(
                    self, 
                    "失败", 
                    f"添加环境变量时发生错误: {str(e)}"
                )
                # 记录错误日志
                self.log_message(f"✗ 添加环境变量失败: {str(e)}\n", "error")
    
    def check_nuitka_installation(self, force=False):
        """检测Nuitka安装状态
        
        通过执行python -m nuitka --version命令来检测Nuitka是否已安装以及其版本。
        如果直接检测失败且检测到是conda环境，则尝试使用conda run命令进行检测。
        根据检测结果记录相应的日志信息。
        
        始终使用用户选择的Python解释器来检测Nuitka版本，避免使用当前环境的Nuitka
        
        Args:
            force (bool): 是否强制重新检测，忽略缓存，默认为False
        """
        # 记录用户操作
        self.log_user_action("点击Nuitka检测按钮", f"强制重新检测: {'是' if force else '否'}")
        
        # 检查是否已有检测线程在运行
        if hasattr(self, 'nuitka_detection_thread') and self.nuitka_detection_thread and self.nuitka_detection_thread.isRunning():
            self.log_message("⚠ Nuitka检测已在进行中...\n", "warning")
            # 记录用户操作
            self.log_user_action("Nuitka检测操作", "检测已在进行中，跳过重复检测")
            return
            
        # 显示加载状态
        self.log_message("🔍 正在检测Nuitka安装状态...\n", "info")
        # 记录用户操作
        self.log_user_action("开始Nuitka检测", "显示加载状态")
        
        # 增加检测计数
        self.total_detection_count += 1
        
        # 生成缓存键
        python_cmd = self.python_combo.currentText().strip() if self.python_combo.currentText().strip() else sys.executable
        cache_params = {
            'python_cmd': python_cmd,
            'timestamp': datetime.now().strftime('%Y-%m-%d')
        }
        cache_key = self._get_cache_key(cache_params)
        
        # 如果不是强制重新检测，则尝试从缓存加载结果
        if not force:
            cached_result = self._load_from_cache(cache_key)
            if cached_result is not None:
                self.log_message(f"{'✓' if cached_result else '⚠'} 使用缓存的Nuitka检测结果\n", 
                               "success" if cached_result else "warning")
                # 记录用户操作
                self.log_user_action("使用缓存结果", f"缓存检测结果: {'成功' if cached_result else '失败'}")
                return cached_result
        
        # 添加调试信息
        self.log_message(f"开始检测Nuitka，使用Python命令: {python_cmd}\n", "info")
        # 记录用户操作
        self.log_user_action("配置检测参数", f"Python命令: {python_cmd}, 强制检测: {force}")
        
        # 创建后台线程执行检测
        thread = NuitkaDetectionThread(python_cmd, force)
        
        # 连接信号
        thread.detection_completed.connect(self._on_nuitka_detection_completed)
        thread.detection_failed.connect(self._on_nuitka_detection_failed)
        thread.log_message.connect(self.log_message)
        thread.detection_started.connect(lambda: self.log_message("🔍 开始Nuitka检测...\n", "info"))
        
        # 保存线程引用并启动
        self.nuitka_detection_thread = thread
        thread.start()
        # 记录用户操作
        self.log_user_action("启动检测线程", "Nuitka检测线程已启动")
            
        return True  # 异步执行，返回True表示检测已启动
    
    def _on_nuitka_detection_completed(self, success):
        """Nuitka检测完成回调
        
        Args:
            success (bool): 检测结果
        """
        # 清理线程引用
        if hasattr(self, 'nuitka_detection_thread'):
            self.nuitka_detection_thread = None
            
        if success:
            self.log_text.append("✓ Nuitka检测完成\n")
            self.log_text.setTextColor(QColor(0, 128, 0))  # 绿色
            # 记录用户操作
            self.log_user_action("Nuitka检测完成", "检测结果: 成功")
        else:
            self.log_text.append("⚠ Nuitka检测失败\n")
            self.log_text.setTextColor(QColor(255, 165, 0))  # 橙色
            # 记录用户操作
            self.log_user_action("Nuitka检测完成", "检测结果: 失败")
    
    def _on_nuitka_detection_failed(self, error_msg):
        """Nuitka检测失败回调
        
        Args:
            error_msg (str): 错误信息
        """
        # 清理线程引用
        if hasattr(self, 'nuitka_detection_thread'):
            self.nuitka_detection_thread = None
            
        self.log_text.append(f"⛔ Nuitka检测异常: {error_msg}\n")
        self.log_text.setTextColor(QColor(255, 0, 0))  # 红色
        # 记录用户操作
        self.log_user_action("Nuitka检测异常", f"错误信息: {error_msg}")
    
    def clear_logs(self):
        """清空日志输出
        
        该方法将清空日志文本框中的所有内容，并记录一条日志消息表示日志已被清空。
        """
        self.log_text.clear()
        self.log_message("✅ 日志已清空\n", "info")
        # 记录用户操作
        self.log_user_action("清空日志", "一键清理所有日志输出")
        
    def export_logs(self):
        """导出日志到文件
        
        该方法将程序运行期间的所有日志内容保存到用户指定的文件中，支持多种文件格式。
        文件名会自动包含时间戳以避免重复，并默认保存在输出目录中。
        包含界面日志、连续日志记录和用户操作记录摘要。
        注意：日志只在用户点击导出时才保存到文件，不会自动保存。
        """
        import datetime
        
        # 获取脚本文件名（如果有）
        script_path = self.script_entry.text().strip()
        # 使用Windows系统默认的路径格式
        script_name = "nuitka_logs"
        if script_path:
            script_name = os.path.splitext(os.path.basename(script_path))[0]
        
        # 生成带日期时间的文件名
        now = datetime.datetime.now()
        timestamp = now.strftime("%Y%m%d_%H%M%S")
        default_filename = f"{script_name}_{timestamp}.log"
        
        # 获取保存目录
        save_dir = self.output_entry.text().strip()
        # 使用Windows系统默认的路径格式
        if not save_dir or not os.path.exists(save_dir):
            save_dir = os.path.dirname(script_path) if script_path else os.getcwd()
        
        default_path = os.path.join(save_dir, default_filename)
        
        # 使用QFileDialog获取保存路径
        path, _ = QFileDialog.getSaveFileName(
            self, 
            "保存日志文件", 
            default_path,
            "Log Files (*.log);;Text Files (*.txt);;All Files (*)"
        )
        
        # 如果用户取消了保存操作，则直接返回
        if not path:
            return
            
        try:
            # 确保文件具有正确的扩展名
            if not path.endswith('.log') and not path.endswith('.txt'):
                path += '.log'
            
            # 获取当前界面显示的日志内容
            log_content = self.log_text.toPlainText()
            
            # 构建完整的日志内容
            full_log_content = ""
            
            # 添加日志文件头信息
            header = f"# Nuitka Packager 日志文件\n"
            header += f"# 生成时间: {now.strftime('%Y-%m-%d %H:%M:%S')}\n"
            header += f"# 导出方式: 手动导出\n"
            header += f"# 连续日志记录: {'启用' if self.continuous_logging else '禁用'}\n"
            header += f"# 用户操作记录: {'启用' if self.user_action_logging else '禁用'}\n"
            header += f"# 缓冲区日志条数: {len(self.log_buffer)}\n"
            header += f"# 用户操作次数: {len(self.user_actions)}\n\n"
            
            full_log_content += header
            
            # 如果日志内容为空，添加提示信息
            if not log_content.strip():
                full_log_content += "# 当前会话暂无日志内容\n"
            else:
                # 添加界面日志内容
                full_log_content += "# === 界面日志内容 ===\n"
                full_log_content += log_content + "\n"
            
            # 添加连续日志内容（如果启用）
            if self.continuous_logging and self.log_buffer:
                full_log_content += "\n# === 连续日志记录 ===\n"
                full_log_content += self.get_continuous_log_content() + "\n"
            
            # 添加用户操作记录摘要（如果启用）
            if self.user_action_logging and self.user_actions:
                full_log_content += "\n# === 用户操作记录摘要 ===\n"
                full_log_content += self.get_user_actions_summary() + "\n"
            
            # 将日志内容写入文件
            with open(path, 'w', encoding='utf-8') as f:
                f.write(full_log_content)
                
            # 记录用户操作
            self.log_user_action("导出日志文件", f"路径: {path}")
                
            # 创建自定义消息框，添加打开日志按钮
            msg_box = CustomMessageBox(self)
            msg_box.setWindowTitle("成功")
            msg_box.setText(f"日志已导出到:\n{path}")
            msg_box.setIcon(QMessageBox.Information)
            
            # 添加打开日志按钮
            open_button = msg_box.addButton("打开日志", QMessageBox.ActionRole)
            
            # 显示消息框
            msg_box.exec()
            
            # 如果用户点击了打开日志按钮
            if msg_box.clickedButton() == open_button:
                try:
                    # 使用系统默认程序打开日志文件
                    os.startfile(path)
                    # 记录用户操作
                    self.log_user_action("打开日志文件", f"路径: {path}")
                except Exception as e:
                    CustomMessageBox.warning(self, "警告", f"无法打开日志文件: {str(e)}")
        except Exception as e:
            # 显示错误消息
            CustomMessageBox.critical(self, "导出失败", f"导出日志时出错:\n{str(e)}")
    
    # ================= 新方法 =================
    
    def open_output_directory(self):
        """打开输出目录
        
        该方法用于在文件管理器中打开用户指定的输出目录。
        支持Windows、macOS和Linux系统，会根据不同的操作系统调用相应的命令。
        """
        # 获取用户设置的输出目录路径
        output_dir = self.output_entry.text().strip()
        # 使用Windows系统默认的路径格式
        
        # 检查是否已设置输出目录
        if not output_dir:
            QMessageBox.warning(self, "警告", "请先设置输出目录")
            return
            
        # 检查输出目录是否存在
        if not os.path.exists(output_dir):
            QMessageBox.warning(self, "警告", "输出目录不存在")
            return
            
        try:
            # Windows系统使用os.startfile方法
            os.startfile(output_dir)
        except Exception as e:
            # 处理打开目录时可能发生的错误
            QMessageBox.critical(self, "错误", f"无法打开目录: {str(e)}")
    
    def show_help(self):
        """显示帮助对话框
        
        该方法创建并显示一个帮助对话框，包含Nuitka EXE打包工具的详细使用说明。
        帮助内容涵盖了工具的主要功能、使用指南、操作流程、常见问题和注意事项。
        """
        # 创建帮助对话框
        help_dialog = QDialog(self)
        help_dialog.setWindowTitle("使用帮助")
        help_dialog.setFixedSize(800, 800)
        
        # 设置对话框布局
        layout = QVBoxLayout(help_dialog)
        
        # 创建文本编辑器用于显示帮助内容
        text = QTextEdit()
        text.setReadOnly(True)
        text.setStyleSheet("background-color: #FFFFFF; color: #4C5270;")
        
        # 从外部模块获取帮助内容
        help_content = get_help_content()

        
        # 设置帮助内容并添加到布局
        text.setHtml(help_content)
        layout.addWidget(text)
        
        # 创建关闭按钮
        close_btn = NeumorphicButton("关闭")
        close_btn.setFixedHeight(self.get_scaled_size(28))   # 与主界面按钮高度一致
        close_btn.setFixedWidth(self.get_scaled_size(80))    # 与主界面按钮宽度一致
        close_btn.clicked.connect(help_dialog.accept)
        layout.addWidget(close_btn, 0, Qt.AlignRight)
        
        # 显示帮助对话框
        help_dialog.exec()
    
    # ================= UPX 检测 =================
    
    def detect_upx(self):
        """检测UPX是否可用并自动设置
        该方法尝试检测系统中是否安装了UPX工具，并自动设置UPX路径。
        如果检测到UPX，会自动填充路径到相应的输入框中。
        """
        # 记录用户操作
        self.log_user_action("UPX检测", "开始检测UPX工具")
        
        try:
            # 尝试查找UPX路径
            # 在Windows系统上，设置启动信息以隐藏命令行窗口
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            # 尝试直接运行upx命令来检测是否安装
            result = subprocess.run(["upx", "--version"], 
                                   stdout=subprocess.PIPE, 
                                   stderr=subprocess.PIPE,
                                   text=True,
                                   encoding='utf-8',
                                   errors='replace',
                                   startupinfo=startupinfo)
            
            # 如果命令执行成功（返回码为0），表示UPX已安装
            if result.returncode == 0:
                # 提取UPX路径
                upx_path = self.find_upx_path()
                if upx_path:
                    # 设置UPX路径到输入框
                    if hasattr(self, 'upx_path_entry') and self.upx_path_entry is not None:
                        self.upx_path_entry.setText(upx_path)
                    # 记录成功日志
                    self.log_message(f"✓ 已自动检测到UPX: {upx_path}\n", "success")
                    # 记录用户操作
                    self.log_user_action("UPX检测", f"检测成功: {upx_path}")
                    
                    # 自动将UPX路径添加到系统PATH环境变量中
                    upx_dir = os.path.dirname(upx_path)
                    current_path = os.environ.get('PATH', '')
                    if upx_dir not in current_path:
                        new_path = f"{upx_dir};{current_path}"
                        os.environ['PATH'] = new_path
                        self.log_message(f"✓ 已将UPX路径添加到环境变量PATH中: {upx_dir}\n", "success")
                        # 记录用户操作
                        self.log_user_action("UPX检测", f"已添加到PATH: {upx_dir}")
                    
                    return True
                else:
                    # 记录警告日志：检测到UPX但无法确定路径
                    self.log_message("⚠ 检测到UPX但无法确定路径\n", "warning")
                    # 记录用户操作
                    self.log_user_action("UPX检测", "检测到UPX但无法确定路径")
                    return False
            else:
                # 记录警告日志：未检测到UPX
                self.log_message("⚠ 未检测到UPX，请手动设置路径\n", "warning")
                # 记录用户操作
                self.log_user_action("UPX检测", "未检测到UPX")
                return False
                
        except FileNotFoundError:
            # 捕获文件未找到异常，记录警告日志
            self.log_message("⚠ 未检测到UPX，请手动设置路径\n", "warning")
            # 记录用户操作
            self.log_user_action("UPX检测", "文件未找到异常")
            return False
        except Exception as e:
            # 捕获其他异常，记录错误日志
            self.log_message(f"⚠ UPX检测错误: {str(e)}\n", "warning")
            # 记录用户操作
            self.log_user_action("UPX检测", f"检测异常: {str(e)}")
            return False
    
    def find_upx_path(self):
        """尝试查找UPX可执行文件路径
        
        该方法会在系统中查找UPX可执行文件的路径。
        在Windows系统上，会检查常见的安装位置；
        在Unix-like系统上，会使用which命令查找。
        
        Returns:
            str or None: UPX可执行文件的完整路径，如果未找到则返回None
        """
        # 定义Windows系统上UPX可能的安装路径
        possible_paths = [
            os.path.join(os.environ.get("ProgramFiles", ""), "upx", "upx.exe"),
            os.path.join(os.environ.get("ProgramFiles(x86)", ""), "upx", "upx.exe"),
            os.path.join(os.environ.get("USERPROFILE", ""), "AppData", "Local", "upx", "upx.exe"),
            os.path.join(os.environ.get("USERPROFILE", ""), "Downloads", "upx", "upx.exe"),
            "C:\\upx\\upx.exe",
            "D:\\upx\\upx.exe"
        ]
        
        # 遍历可能的路径，检查文件是否存在
        for path in possible_paths:
            if os.path.exists(path):
                return path
        
        # 尝试通过where命令查找
        try:
            # Windows系统使用where命令
            cmd = "where upx"
            # 执行命令查找UPX路径
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True, 
                                  encoding='utf-8', errors='replace')
            # 如果命令执行成功，返回找到的路径
            if result.returncode == 0:
                return result.stdout.strip()
        except:
            # 忽略查找过程中可能出现的异常
            pass
        
        # 如果未找到UPX路径，返回None
        return None
    
    # ================= Python包查询方法 =================
    
    def query_python_packages(self):
        """查询已选择Python解释器环境中的原装包
        
        该方法会查询当前选择的Python解释器环境中安装的所有包，
        并将结果显示在日志输出区域。
        """
        # 获取当前选择的Python解释器路径
        python_cmd = self.python_combo.currentText().strip()
        if not python_cmd:
            self.log_message("❌ 请先选择Python解释器\n", "error")
            return
            
        # 记录用户操作
        self.log_user_action("Python包查询", f"开始查询包信息，使用解释器: {python_cmd}")
        
        self.log_message("🔍 开始查询Python环境中的原装包...\n", "info")
        self.log_message(f"📋 使用Python解释器: {python_cmd}\n", "info")
        
        try:
            # 检查是否为conda环境
            conda_env_name = self._get_conda_env_name(python_cmd)
            
            if conda_env_name:
                # 如果是conda环境，使用conda list命令
                self.log_message(f"🐍 检测到conda环境: {conda_env_name}\n", "info")
                self.log_message("📋 使用mamba list查询包信息...\n", "info")
                # 记录用户操作
                self.log_user_action("Python包查询", f"检测到conda环境: {conda_env_name}")
                
                # 构建mamba list命令
                if sys.platform == "win32":
                    # Windows系统下需要先激活conda环境
                    cmd = f'conda activate {conda_env_name} && mamba list'
                else:
                    # Linux/macOS系统
                    cmd = f'conda activate {conda_env_name} && mamba list'
                
                self.log_message(f"执行命令: {cmd}\n", "debug")
                
                # 执行命令，使用更健壮的编码处理
                try:
                    result = subprocess.run(cmd, shell=True, capture_output=True, text=True, 
                                          encoding='utf-8', errors='replace')
                except UnicodeDecodeError:
                    # 如果UTF-8解码失败，尝试使用系统默认编码
                    result = subprocess.run(cmd, shell=True, capture_output=True, text=True, 
                                          encoding='gbk', errors='replace')
                
                self.log_message(f"返回码: {result.returncode}\n", "debug")
                self.log_message(f"标准输出长度: {len(result.stdout) if result.stdout else 0}\n", "debug")
                self.log_message(f"标准错误长度: {len(result.stderr) if result.stderr else 0}\n", "debug")
                
                if result.returncode == 0:
                    # 解析conda list输出
                    try:
                        packages = self._parse_conda_list_output(result.stdout)
                        self._display_packages(packages, "conda")
                        # 记录用户操作
                        self.log_user_action("Python包查询", "conda包查询成功")
                    except Exception as parse_error:
                        self.log_message(f"❌ 解析conda list输出时发生错误: {str(parse_error)}\n", "error")
                        self.log_message(f"原始输出: {repr(result.stdout[:500])}\n", "debug")
                        # 记录用户操作
                        self.log_user_action("Python包查询", f"解析conda输出失败: {str(parse_error)}")
                else:
                    self.log_message(f"❌ mamba list执行失败: {result.stderr}\n", "error")
                    # 记录用户操作
                    self.log_user_action("Python包查询", f"mamba list执行失败: {result.stderr}")
                    # 尝试使用pip list作为备选方案
                    self._query_packages_with_pip(python_cmd)
            else:
                # 非conda环境，使用pip list命令
                self.log_message("📋 使用pip list查询包信息...\n", "info")
                # 记录用户操作
                self.log_user_action("Python包查询", "使用pip list查询包信息")
                self._query_packages_with_pip(python_cmd)
                
        except Exception as e:
            self.log_message(f"❌ 查询包信息时发生错误: {str(e)}\n", "error")
            import traceback
            self.log_message(f"详细错误信息:\n{traceback.format_exc()}\n", "debug")
            # 记录用户操作
            self.log_user_action("Python包查询", f"查询异常: {str(e)}")
    
    def _get_conda_env_name(self, python_cmd):
        """获取Python解释器对应的conda环境名称
        
        Args:
            python_cmd (str): Python解释器路径
            
        Returns:
            str or None: conda环境名称，如果不是conda环境则返回None
        """
        try:
            # 检查Python路径是否包含conda或envs
            if 'conda' in python_cmd.lower() or 'envs' in python_cmd.lower():
                # 从路径中提取环境名称
                if 'envs' in python_cmd:
                    # 格式: .../envs/env_name/python.exe
                    env_name = os.path.basename(os.path.dirname(python_cmd))
                    return env_name
                else:
                    # 可能是base环境
                    return 'base'
            return None
        except:
            return None
    
    def _query_packages_with_pip(self, python_cmd):
        """使用pip list查询包信息
        
        Args:
            python_cmd (str): Python解释器路径
        """
        # 记录用户操作
        self.log_user_action("Python包查询", f"使用pip查询包信息，解释器: {python_cmd}")
        
        # 执行命令的多种方式
        execution_methods = []
        
        # 构建pip命令的多种执行方式
        if sys.platform == "win32":
            # Windows系统 - 构建多种执行方式
            # 方法1: 直接调用Scripts目录下的pip.exe
            scripts_dir = os.path.join(os.path.dirname(python_cmd), 'Scripts')
            pip_exe = os.path.join(scripts_dir, 'pip.exe')
            if os.path.exists(pip_exe):
                execution_methods.append([pip_exe])
                self.log_message(f"📋 检测到pip.exe: {pip_exe}\n", "debug")
            
            # 方法2: 使用python -m pip方式
            execution_methods.append([python_cmd, '-m', 'pip'])
            
            # 方法3: 使用python -m pip方式（处理包含空格的路径）
            execution_methods.append([python_cmd, '-m', 'pip'])
        else:
            # Linux/macOS系统
            bin_dir = os.path.join(os.path.dirname(python_cmd), 'bin')
            pip_exe = os.path.join(bin_dir, 'pip')
            if os.path.exists(pip_exe):
                execution_methods.append([pip_exe])
            execution_methods.append([python_cmd, '-m', 'pip'])
        
        # 确保至少有一个执行方式
        if not execution_methods:
            execution_methods = [[python_cmd, '-m', 'pip']]
        
        # 尝试所有执行方式
        for cmd_base in execution_methods:
            try:
                # 完整命令（添加list参数）
                cmd = cmd_base + ['list']
                
                # 记录命令信息
                self.log_message(f"执行pip命令: {' '.join(cmd)}\n", "debug")
                
                # 设置启动信息（Windows下隐藏命令窗口）
                startupinfo = None
                if sys.platform == "win32":
                    startupinfo = subprocess.STARTUPINFO()
                    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                    startupinfo.wShowWindow = 0
                
                # 尝试使用不同的编码执行命令
                encodings = ['utf-8', 'gbk', 'cp936', 'latin-1']
                result = None
                
                for encoding in encodings:
                    try:
                        # 创建环境变量副本，添加必要的路径
                        env = os.environ.copy()
                        # 添加Python所在目录和Scripts目录到PATH
                        python_dir = os.path.dirname(python_cmd)
                        if sys.platform == "win32":
                            scripts_path = os.path.join(python_dir, 'Scripts')
                            env['PATH'] = f"{scripts_path};{python_dir};{env.get('PATH', '')}"
                        else:
                            bin_path = os.path.join(python_dir, 'bin')
                            env['PATH'] = f"{bin_path}:{python_dir}:{env.get('PATH', '')}"
                        
                        # 执行命令
                        result = subprocess.run(
                            cmd,
                            capture_output=True,
                            text=True,
                            encoding=encoding,
                            errors='replace',
                            startupinfo=startupinfo,
                            shell=False,
                            env=env,
                            timeout=30  # 添加超时保护
                        )
                        break  # 如果成功，跳出编码循环
                    except UnicodeDecodeError:
                        continue  # 尝试下一个编码
                    except Exception as encode_e:
                        self.log_message(f"编码 {encoding} 执行失败: {str(encode_e)}\n", "debug")
                        continue
                
                if result:
                    self.log_message(f"pip返回码: {result.returncode}\n", "debug")
                    self.log_message(f"pip标准输出长度: {len(result.stdout) if result.stdout else 0}\n", "debug")
                    
                    if result.returncode == 0:
                        # 解析pip list输出
                        try:
                            packages = self._parse_pip_list_output(result.stdout)
                            self._display_packages(packages, "pip")
                            # 记录用户操作
                            self.log_user_action("Python包查询", "pip包查询成功")
                            return  # 成功后直接返回
                        except Exception as parse_error:
                            self.log_message(f"❌ 解析pip list输出时发生错误: {str(parse_error)}\n", "error")
                            self.log_message(f"原始输出: {repr(result.stdout[:500])}\n", "debug")
                            # 记录用户操作
                            self.log_user_action("Python包查询", f"解析pip输出失败: {str(parse_error)}")
                            continue  # 尝试下一个执行方式
                    else:
                        self.log_message(f"❌ pip list执行失败(返回码: {result.returncode}): {result.stderr}\n", "error")
                        continue  # 尝试下一个执行方式
                        
            except PermissionError:
                # 处理权限错误
                self.log_message(f"⚠ 权限错误，尝试其他执行方式\n", "warning")
                continue  # 尝试下一个执行方式
            except Exception as e:
                self.log_message(f"❌ 执行命令时出错: {str(e)}\n", "error")
                continue  # 尝试下一个执行方式
        
        # 所有方式都失败了
        self.log_message(f"❌ 所有pip执行方式都失败了\n", "error")
        self.log_user_action("Python包查询", "所有pip执行方式都失败")
        
        # 尝试最后的备选方案：使用pip freeze
        try:
            self.log_message("尝试使用pip freeze作为备选方案...\n", "info")
            cmd = [python_cmd, '-m', 'pip', 'freeze']
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                encoding='utf-8',
                errors='replace',
                shell=False,
                timeout=30
            )
            
            if result.returncode == 0:
                # 解析pip freeze输出
                try:
                    packages = []
                    for line in result.stdout.strip().split('\n'):
                        if '==' in line:
                            name, version = line.split('==', 1)
                            packages.append({'name': name, 'version': version})
                    
                    if packages:
                        self._display_packages(packages, "pip freeze")
                        self.log_user_action("Python包查询", "pip freeze查询成功")
                        return
                except Exception as parse_error:
                    self.log_message(f"❌ 解析pip freeze输出失败: {str(parse_error)}\n", "error")
        except Exception as e:
            self.log_message(f"❌ pip freeze执行失败: {str(e)}\n", "error")
    
    def _parse_conda_list_output(self, output):
        """解析conda list命令的输出
        
        Args:
            output (str): conda list命令的输出
            
        Returns:
            list: 包信息列表，每个元素为(包名, 版本, 构建信息, 通道)的元组
        """
        packages = []
        if not output:
            return packages
            
        lines = output.strip().split('\n')
        if len(lines) < 3:
            return packages
        
        # 跳过标题行和分隔线，从第3行开始
        for line in lines[2:]:
            line = line.strip()
            if line and not line.startswith('#'):
                # 解析包信息，conda list输出格式: 包名 版本 构建信息 通道
                parts = line.split()
                if len(parts) >= 2:
                    package_name = parts[0]
                    version = parts[1]
                    build_info = parts[2] if len(parts) > 2 else ''
                    channel = parts[3] if len(parts) > 3 else ''
                    packages.append((package_name, version, build_info, channel))
        
        return packages
    
    def _parse_pip_list_output(self, output):
        """解析pip list命令的输出
        
        Args:
            output (str): pip list命令的输出
            
        Returns:
            list: 包信息列表，每个元素为(包名, 版本)的元组
        """
        packages = []
        if not output:
            return packages
            
        lines = output.strip().split('\n')
        if len(lines) < 3:
            return packages
        
        # 跳过标题行和分隔线，从第3行开始
        for line in lines[2:]:
            line = line.strip()
            if line and not line.startswith('#'):
                # 解析包信息，pip list输出格式: 包名 版本
                parts = line.split()
                if len(parts) >= 2:
                    package_name = parts[0]
                    version = parts[1]
                    packages.append((package_name, version))
        
        return packages
    
    def _display_packages(self, packages, source_type):
        """在日志中显示包信息
        
        Args:
            packages (list): 包信息列表
            source_type (str): 包来源类型（"conda"或"pip"）
        """
        if not packages:
            self.log_message("⚠ 未找到任何已安装的包\n", "warning")
            return
        
        self.log_message(f"\n📦 找到 {len(packages)} 个已安装的包 (来源: {source_type}):\n", "info")
        self.log_message("=" * 80 + "\n", "info")
        
        if source_type == "conda":
            # conda包信息显示格式
            self.log_message(f"{'包名':<20} {'版本':<15} {'构建信息':<20} {'通道':<20}\n", "info")
            self.log_message("-" * 80 + "\n", "info")
            for package_name, version, build_info, channel in packages:
                self.log_message(f"{package_name:<20} {version:<15} {build_info:<20} {channel:<20}\n", "info")
        else:
            # pip包信息显示格式
            self.log_message(f"{'包名':<30} {'版本':<15}\n", "info")
            self.log_message("-" * 50 + "\n", "info")
            for package_name, version in packages:
                self.log_message(f"{package_name:<30} {version:<15}\n", "info")
        
        self.log_message("=" * 80 + "\n", "info")
        self.log_message("✅ 包查询完成\n", "success")
    
    # ================= 依赖扫描方法 =================
    
    def scan_dependencies(self):
        """扫描项目依赖
        
        该方法使用modulefinder模块分析Python脚本的导入语句，
        自动识别项目依赖的外部模块，并提供用户界面让用户选择需要添加的依赖。
        """
        # 获取用户输入的主脚本路径
        script_path = self.script_entry.text().strip()
        # 使用Windows系统默认的路径格式
        
        # 检查是否已选择主脚本文件
        if not script_path:
            QMessageBox.warning(self, "警告", "请先选择主脚本文件")
            # 记录用户操作
            self.log_user_action("依赖扫描", "未选择主脚本文件")
            return
            
        # 检查主脚本文件是否存在
        if not os.path.exists(script_path):
            QMessageBox.warning(self, "警告", "主脚本文件不存在")
            # 记录用户操作
            self.log_user_action("依赖扫描", f"主脚本文件不存在: {script_path}")
            return
            
        # 检查是否已有依赖扫描线程在运行
        if hasattr(self, 'dependency_scan_thread') and self.dependency_scan_thread and self.dependency_scan_thread.isRunning():
            self.log_message("⚠ 依赖扫描已在进行中...\n", "warning")
            # 记录用户操作
            self.log_user_action("依赖扫描", "依赖扫描已在进行中")
            return
        
        # 记录用户操作
        self.log_user_action("依赖扫描", f"开始扫描依赖，主脚本: {script_path}")
        
        # 创建后台线程执行依赖扫描
        thread = DependencyScanThread(script_path)
        self.dependency_scan_thread = thread  # 保存线程引用
        
        # 连接信号
        thread.scan_completed.connect(self._on_dependency_scan_completed)
        thread.scan_failed.connect(self._on_dependency_scan_failed)
        thread.log_message.connect(self.log_message)
        
        # 启动线程
        thread.start()
    
    def _on_dependency_scan_completed(self, custom_modules):
        """依赖扫描完成回调
        
        Args:
            custom_modules (list): 找到的外部依赖模块列表
        """
        # 清理线程引用
        if hasattr(self, 'dependency_scan_thread'):
            self.dependency_scan_thread = None
            
        # 记录用户操作
        self.log_user_action("依赖扫描", f"扫描完成，找到 {len(custom_modules)} 个外部依赖")
            
        # 如果找到依赖，显示给用户选择
        if custom_modules:
            # 记录找到的依赖数量
            self.log_message(f"找到 {len(custom_modules)} 个可能的外部依赖:\n")
            
            # 创建依赖选择对话框
            dialog = QDialog(self)
            dialog.setWindowTitle("选择要添加的依赖")
            dialog.setMinimumSize(500, 400)
            
            # 设置对话框布局
            layout = QVBoxLayout()
            
            # 添加标签
            label = QLabel("请选择要添加的外部依赖模块:")
            layout.addWidget(label)
            
            # 创建列表控件并添加模块列表
            list_widget = QListWidget()
            list_widget.setSelectionMode(QListWidget.MultiSelection)
            list_widget.addItems(sorted(set(custom_modules)))  # 去重
            
            # 添加全选按钮
            select_all_layout = QHBoxLayout()
            select_all_btn = NeumorphicButton("全选")
            select_all_btn.clicked.connect(lambda: list_widget.selectAll())
            select_all_layout.addWidget(select_all_btn)
            
            deselect_all_btn = NeumorphicButton("取消全选")
            deselect_all_btn.clicked.connect(lambda: list_widget.clearSelection())
            select_all_layout.addWidget(deselect_all_btn)
            
            layout.addLayout(select_all_layout)
            layout.addWidget(list_widget)
            
            # 添加确定和取消按钮
            button_layout = QHBoxLayout()
            ok_btn = NeumorphicButton("确定")
            cancel_btn = NeumorphicButton("取消")
            ok_btn.clicked.connect(dialog.accept)
            cancel_btn.clicked.connect(dialog.reject)
            button_layout.addWidget(ok_btn)
            button_layout.addWidget(cancel_btn)
            layout.addLayout(button_layout)
            
            dialog.setLayout(layout)
            
            # 显示对话框并处理用户选择
            if dialog.exec() == QDialog.Accepted:
                selected_items = list_widget.selectedItems()
                if selected_items:
                    count = 0
                    for item in selected_items:
                        module = item.text()
                        dep_item = f"{self.MODULE_PREFIX}{module}"
                        
                        # 检查是否已存在
                        existing = [self.deps_list.item(i).text() for i in range(self.deps_list.count())]
                        if dep_item not in existing:
                            self.deps_list.addItem(dep_item)
                            self.log_message(f"添加模块: {module}\n")
                            count += 1
                    
                    # 记录成功添加的依赖数量
                    self.log_message(f"\n✅ 成功添加 {count} 个依赖模块\n")
                    # 记录用户操作
                    self.log_user_action("依赖扫描", f"成功添加 {count} 个依赖模块")
                else:
                    # 记录未选择任何依赖
                    self.log_message("未选择任何依赖模块\n")
                    # 记录用户操作
                    self.log_user_action("依赖扫描", "未选择任何依赖模块")
            else:
                # 记录用户取消操作
                self.log_message("用户取消操作\n")
                # 记录用户操作
                self.log_user_action("依赖扫描", "用户取消依赖选择")
        else:
            # 记录未发现需要添加的外部依赖模块
            self.log_message("未发现需要添加的外部依赖模块\n")
            # 记录用户操作
            self.log_user_action("依赖扫描", "未发现需要添加的外部依赖")
        
        # 记录依赖扫描完成
        self.log_message("依赖扫描完成\n")
    
    def _on_dependency_scan_failed(self, error_msg):
        """依赖扫描失败回调
        
        Args:
            error_msg (str): 错误信息
        """
        # 清理线程引用
        if hasattr(self, 'dependency_scan_thread'):
            self.dependency_scan_thread = None
            
        QMessageBox.critical(self, "扫描错误", f"依赖扫描失败: {error_msg}")
        self.log_message(f"⛔ 依赖扫描失败: {error_msg}\n", "error")
        # 记录用户操作
        self.log_user_action("依赖扫描", f"扫描失败: {error_msg}")
    
    # ================= 更新方法 =================
    
    def update_mode(self, mode):
        """更新编译模式
        
        该方法用于更新Nuitka的编译模式，可选值为'file'（文件模式）或'module'（模块模式）。
        
        Args:
            mode (str): 编译模式，'file' 或 'module'
        """
        # 更新编译模式变量
        self.mode_var = mode
    
    def update_platform(self, platform):
        """更新目标平台设置
        
        该方法用于更新编译的目标平台。当前版本固定为Windows平台。
        同时会更新控制台设置选项的可见性和可用性。
        
        Args:
            platform (str): 目标平台，当前固定为"windows"
        """
        # 固定为Windows平台
        self.platform_var = "windows"
        
        # Windows平台下控制台设置可用
        if hasattr(self, 'console_enable_rb') and self.console_enable_rb is not None:
            self.console_enable_rb.setVisible(True)
            self.console_enable_rb.setEnabled(True)
        if hasattr(self, 'console_disable_rb') and self.console_disable_rb is not None:
            self.console_disable_rb.setVisible(True)
            self.console_disable_rb.setEnabled(True)
    
    def update_opt(self, opt):
        """更新优化级别
        
        该方法用于更新Nuitka的优化级别设置。
        
        Args:
            opt (str): 优化级别，如"noinline", "noasserts", "norandomization"等
        """
        # 更新优化级别变量
        self.opt_var = opt
    
    def update_jobs(self, value):
        """更新并行任务数
        
        该方法用于更新Nuitka编译时的并行任务数，并更新界面上的显示。
        
        Args:
            value (int): 并行任务数
        """
        # 更新任务数变量
        self.jobs_var = value
        # 更新界面上的任务数显示
        self.jobs_label.setText(f"任务数: {value} / {os.cpu_count()}")
    
    def update_lto(self, lto_level):
        """更新LTO优化等级
        
        该方法用于更新LTO（Link Time Optimization）优化等级。
        
        Args:
            lto_level (str): LTO优化等级 (off/yes/thin/full)
        """
        # 更新LTO优化等级变量
        self.lto_var = lto_level
    
    def update_compiler(self, compiler):
        """更新编译器选择
        
        该方法用于更新C编译器的选择。
        
        Args:
            compiler (str): 编译器名称，如"mingw64", "clang"等
        """
        # 更新编译器变量
        self.compiler_var = compiler
    
    def update_console(self, console):
        """更新控制台设置
        
        该方法用于更新编译后可执行文件的控制台行为。
        
        Args:
            console (str): 控制台设置，"enable"表示启用控制台，"disable"表示禁用控制台
        """
        # 更新控制台设置变量
        self.console_var = console
    
    # update_arch方法已移除，因为只支持Windows平台
    

    
    def toggle_upx(self, state):
        """切换UPX压缩选项
        
        该方法用于切换是否启用UPX压缩功能。当启用时会检查UPX是否可用，
        并在插件列表中选择UPX插件；当禁用时会取消选择UPX插件。
        
        Args:
            state (bool): UPX启用状态，True表示启用，False表示禁用
        """
        # 更新UPX启用状态变量
        self.upx_var = state
        
        if state:
            # 当启用UPX时，检查UPX是否在环境变量中（包括系统和用户环境变量）
            if not self.is_upx_in_path():
                # 更详细的警告信息，指导用户如何设置UPX路径
                self.log_message("⚠ 环境变量中未检测到UPX，请选择UPX可执行文件并设置环境变量\n", "warning")
                self.log_message("⚠ 请在UPX路径输入框中选择UPX.exe文件，然后点击'设置path'按钮\n", "warning")
                self.log_message("⚠ 设置后需要重启应用程序使环境变量生效\n", "warning")
                self.log_message("⚠ 如果您已设置环境变量但仍提示未检测到，请检查：\n", "warning")
                self.log_message("⚠ 1. UPX.exe文件是否确实在PATH环境变量指定的目录中\n", "warning")
                self.log_message("⚠ 2. 应用程序是否已重启使新的环境变量生效\n", "warning")
            else:
                self.log_message("✓ 已检测到UPX在环境变量中，可以直接使用\n", "success")
            
            # 在插件列表中选择UPX插件
            for i in range(self.plugin_list.count()):
                if self.plugin_list.item(i).text() == "upx":
                    self.plugin_list.item(i).setSelected(True)
                    break
        else:
            # 当禁用UPX时，取消选择UPX插件
            for i in range(self.plugin_list.count()):
                if self.plugin_list.item(i).text() == "upx":
                    self.plugin_list.item(i).setSelected(False)
                    break
    
    def is_upx_in_path(self):
        """检查UPX是否在环境变量PATH中
        
        该方法通过两种方式检查UPX是否在环境变量PATH中（包括系统和用户环境变量）：
        1. 尝试运行UPX命令
        2. 直接检查PATH环境变量中的所有目录是否包含upx.exe文件
        
        Returns:
            bool: 如果UPX在PATH中返回True，否则返回False
        """
        # 方法1：尝试运行UPX命令
        try:
            # 调用UPX，隐藏命令行窗口
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            startupinfo.wShowWindow = 0
            
            # 尝试运行UPX命令检查是否可用
            subprocess.run(["upx", "-version"], 
                          stdout=subprocess.DEVNULL, 
                          stderr=subprocess.DEVNULL,
                          startupinfo=startupinfo,
                          timeout=5)  # 添加超时限制
            return True
        except:
            # 如果运行失败，尝试方法2
            pass
        
        # 方法2：直接检查PATH环境变量中的所有目录是否包含upx.exe
        try:
            # 获取环境变量PATH
            path_env = os.environ.get("PATH", "")
            # 分割PATH为目录列表
            path_dirs = path_env.split(os.pathsep)
            
            # 检查每个目录是否包含upx.exe
            for path_dir in path_dirs:
                if not path_dir:  # 跳过空目录
                    continue
                
                # 检查upx.exe是否存在于该目录
                upx_path = os.path.join(path_dir, "upx.exe")
                if os.path.isfile(upx_path):
                    return True
        except:
            # 如果检查失败，返回False
            pass
        
        return False
    
    # ================= UPX 路径设置 =================
    
    def set_upx_path(self):
        """设置UPX路径
        
        该方法用于将用户选择的UPX可执行文件所在目录添加到系统PATH环境变量中，
        使Nuitka能够找到并使用UPX进行可执行文件压缩。
        """
        # 获取用户输入的UPX路径
        upx_path = self.upx_path_entry.text().strip()
        
        # 检查是否已选择UPX可执行文件
        if not upx_path:
            QMessageBox.warning(self, "警告", "请先选择UPX可执行文件")
            return
            
        # 获取UPX目录路径
        upx_dir = os.path.dirname(upx_path)
        
        # 检查目录是否存在
        if not os.path.isdir(upx_dir):
            QMessageBox.critical(self, "错误", f"目录不存在: {upx_dir}")
            return
            
        try:
            # 获取当前系统PATH环境变量
            env_path = os.environ["PATH"]
            
            # 检查目录是否已在PATH中
            if upx_dir in env_path.split(os.pathsep):
                QMessageBox.information(self, "提示", "该目录已在系统PATH中")
                return
            
            # 1. 先修改当前进程的环境变量，使其立即生效
            os.environ["PATH"] = f"{upx_dir}{os.pathsep}{os.environ['PATH']}"
            
            # 2. 使用setx命令将路径添加到用户环境变量（不需要管理员权限）
            import ctypes
            import sys
            
            # 使用更安全的方式构建setx命令，避免路径中的特殊字符问题
            # 使用-m参数确保添加到用户环境变量，而不是系统环境变量
            # 分别设置参数，避免在一个字符串中混合展开变量
            
            # 将UPX路径设置到系统环境变量（需要管理员权限）
            # 使用/M参数表示设置系统环境变量
            # 先检查是否以管理员权限运行
            import ctypes
            is_admin = ctypes.windll.shell32.IsUserAnAdmin() != 0
            
            if is_admin:
                # 以管理员权限运行，可以设置系统环境变量
                current_path = os.environ.get("PATH", "")
                new_path = f"{upx_dir}{os.pathsep}{current_path}"
                
                result = subprocess.run(
                    ["cmd.exe", "/c", 
                     "setx", "/M", "PATH", new_path],
                    capture_output=True,
                    text=True
                )
            else:
                # 没有管理员权限，先尝试设置用户环境变量
                current_path = os.environ.get("PATH", "")
                new_path = f"{upx_dir}{os.pathsep}{current_path}"
                
                result = subprocess.run(
                    ["cmd.exe", "/c", 
                     "setx", "PATH", new_path],
                    capture_output=True,
                    text=True
                )
                
                # 记录没有管理员权限的提示
                self.log_message("⚠ 没有管理员权限，已将UPX路径添加到用户环境变量中（需要重启电脑才能在所有应用中生效）\n", "warning")
            
            # 检查是否添加成功
            if result.returncode == 0:
                if is_admin:
                    self.log_message(f"✓ 已将UPX路径添加到系统环境变量中: {upx_dir}\n", "success")
                    message_title = "成功"
                    message_content = "UPX目录已添加到系统环境变量\n提示：需要重启当前进程才能使环境变量生效"
                else:
                    self.log_message(f"✓ 已将UPX路径添加到用户环境变量中: {upx_dir}\n", "success")
                    message_title = "提示"
                    message_content = "UPX目录已添加到用户环境变量\n提示1：需要重启应用程序才能使UPX在当前会话中生效\n提示2：需要重启电脑才能在所有应用中生效\n提示3：若要添加到系统环境变量，请以管理员身份运行本程序"
                
                # 验证UPX是否可用
                if self.is_upx_in_path():
                    QMessageBox.information(self, message_title, message_content)
                else:
                    QMessageBox.information(self, message_title, f"{message_content}\n\n当前进程中仍无法检测到UPX，请重启应用程序后再试")
            else:
                # 如果setx失败，可能是因为路径太长导致的
                # 这时至少确保当前进程可以使用
                self.log_message(f"⚠ 环境变量添加失败，但已添加到当前进程: {result.stderr}\n", "warning")
                
                if not is_admin:
                    QMessageBox.information(self, "部分成功", "无法修改用户环境变量，但已将路径添加到当前进程\n建议1：以管理员身份运行本程序，然后再次设置UPX路径\n建议2：手动添加UPX路径到系统环境变量")
                else:
                    QMessageBox.information(self, "部分成功", "无法修改系统环境变量，但已将路径添加到当前进程\n请考虑手动添加UPX路径到系统环境变量")
                
        except Exception as e:
            self.log_message(f"✗ 添加UPX路径失败: {str(e)}\n", "error")
            QMessageBox.critical(self, "错误", f"添加PATH失败: {str(e)}")
    



    def convert_to_ico(self):
        """转换图标为ICO格式
        
        该方法用于将用户选择的图标文件转换为Windows可执行文件所需的ICO格式。
        转换后的文件会保存在原文件相同目录下，文件名保持一致，扩展名改为.ico。
        如果目标文件已存在，会询问用户是否覆盖。
        """
        # 获取用户选择的图标路径
        icon_path = self.icon_entry.text()
        # 使用Windows系统默认的路径格式
        
        # 检查是否已选择图标文件
        if not icon_path:
            # 创建自定义警告对话框，设置按钮文本为"确认"
            msg_box = QMessageBox(self)
            msg_box.setIcon(QMessageBox.Warning)
            msg_box.setWindowTitle("警告")
            msg_box.setText("请先选择要转换的图标文件")
            
            # 设置按钮文本为"确认"
            ok_button = msg_box.addButton("确认", QMessageBox.AcceptRole)
            
            # 应用统一样式
            if hasattr(self, 'dpi_scale'):
                dpi_scale = self.dpi_scale
            else:
                screen = QApplication.primaryScreen()
                dpi_scale = screen.logicalDotsPerInch() / 96.0
            
            # 设置字体
            font = msg_box.font()
            font.setFamily("Microsoft YaHei")
            font.setPointSize(int(12 * dpi_scale))
            msg_box.setFont(font)
            
            # 显示对话框
            msg_box.exec()
            return
            
        # 检查文件是否已经是ICO格式
        if icon_path.lower().endswith(".ico"):
            # 创建自定义信息对话框，设置按钮文本为"确认"
            msg_box = QMessageBox(self)
            msg_box.setIcon(QMessageBox.Information)
            msg_box.setWindowTitle("提示")
            msg_box.setText("文件已经是ICO格式")
            
            # 设置按钮文本为"确认"
            ok_button = msg_box.addButton("确认", QMessageBox.AcceptRole)
            
            # 应用统一样式
            if hasattr(self, 'dpi_scale'):
                dpi_scale = self.dpi_scale
            else:
                screen = QApplication.primaryScreen()
                dpi_scale = screen.logicalDotsPerInch() / 96.0
            
            # 设置字体
            font = msg_box.font()
            font.setFamily("Microsoft YaHei")
            font.setPointSize(int(12 * dpi_scale))
            msg_box.setFont(font)
            
            # 显示对话框
            msg_box.exec()
            return
        
        # === 关键修改：自动生成新文件名 ===
        # 获取原文件的目录和文件名（不含扩展名）
        dir_name = os.path.dirname(icon_path)
        base_name = os.path.splitext(os.path.basename(icon_path))[0]
        # 生成新路径：原目录 + 原文件名 + .ico
        new_ico_path = os.path.join(dir_name, f"{base_name}.ico")
        
        # 可选：如果文件已存在，询问是否覆盖
        if os.path.exists(new_ico_path):
            # 创建自定义询问对话框，设置按钮文本为中文
            msg_box = QMessageBox(self)
            msg_box.setIcon(QMessageBox.Question)
            msg_box.setWindowTitle("覆盖确认")
            msg_box.setText(f"文件 {new_ico_path} 已存在，是否覆盖？")
            
            # 设置按钮文本为中文
            yes_button = msg_box.addButton("是", QMessageBox.YesRole)
            no_button = msg_box.addButton("否", QMessageBox.NoRole)
            msg_box.setDefaultButton(no_button)  # 默认选中"否"按钮
            
            # 应用统一样式
            if hasattr(self, 'dpi_scale'):
                dpi_scale = self.dpi_scale
            else:
                screen = QApplication.primaryScreen()
                dpi_scale = screen.logicalDotsPerInch() / 96.0
            
            # 设置字体
            font = msg_box.font()
            font.setFamily("Microsoft YaHei")
            font.setPointSize(int(12 * dpi_scale))
            msg_box.setFont(font)
            
            # 显示对话框并获取结果
            msg_box.exec()
            
            # 判断用户选择
            if msg_box.clickedButton() == no_button:
                return

        # ================================

        try:
            # 打开原图标文件并转换为ICO格式
            with Image.open(icon_path) as img:
                # 转换为合适的尺寸和格式
                img = img.resize((256, 256), Image.LANCZOS)
                img.save(new_ico_path, format="ICO", sizes=[(256, 256)])
            
            # 更新界面显示为新生成的 .ico 文件路径
            self.icon_entry.setText(new_ico_path)
            
            # 创建自定义成功提示对话框，设置按钮文本为"确认"
            msg_box = QMessageBox(self)
            msg_box.setIcon(QMessageBox.Information)
            msg_box.setWindowTitle("成功")
            msg_box.setText(f"图标已成功转换为ICO格式\n保存位置：{new_ico_path}")
            
            # 设置按钮文本为"确认"
            ok_button = msg_box.addButton("确认", QMessageBox.AcceptRole)
            
            # 应用统一样式
            if hasattr(self, 'dpi_scale'):
                dpi_scale = self.dpi_scale
            else:
                screen = QApplication.primaryScreen()
                dpi_scale = screen.logicalDotsPerInch() / 96.0
            
            # 设置字体
            font = msg_box.font()
            font.setFamily("Microsoft YaHei")
            font.setPointSize(int(12 * dpi_scale))
            msg_box.setFont(font)
            
            # 显示对话框
            msg_box.exec()
            
        except Exception as e:
            # 创建自定义错误提示对话框，设置按钮文本为"确认"
            msg_box = QMessageBox(self)
            msg_box.setIcon(QMessageBox.Critical)
            msg_box.setWindowTitle("转换错误")
            msg_box.setText(f"图标转换失败: {str(e)}")
            
            # 设置按钮文本为"确认"
            ok_button = msg_box.addButton("确认", QMessageBox.AcceptRole)
            
            # 应用统一样式
            if hasattr(self, 'dpi_scale'):
                dpi_scale = self.dpi_scale
            else:
                screen = QApplication.primaryScreen()
                dpi_scale = screen.logicalDotsPerInch() / 96.0
            
            # 设置字体
            font = msg_box.font()
            font.setFamily("Microsoft YaHei")
            font.setPointSize(int(12 * dpi_scale))
            msg_box.setFont(font)
            
            # 显示对话框
            msg_box.exec()












    
    # ================= 依赖管理方法 =================
    
    def add_module(self):
        """添加Python模块依赖
        
        该方法支持批量添加多个模块，用户可以输入一个或多个模块名。
        支持使用逗号、分号或换行符分隔多个模块名。
        """
        # 直接进入批量添加模式
        # 批量添加模式 - 使用自定义对话框以支持样式设置
        dialog = QDialog(self)
        dialog.setWindowTitle("批量添加模块")
        # dialog.resize(500, 500)  # 设置初始尺寸为500x500，允许用户拖拽调整
        # 固定大小
        dialog.setFixedSize(400, 650)  # 设置固定尺寸
        dialog.setMinimumSize(400, 400)  # 设置最小尺寸
        
        # 设置对话框样式
        dialog.setStyleSheet("""
            QDialog {
                background-color: #E3F2FD;  /* 天蓝色背景 */
                font-family: "Microsoft YaHei", "SimHei";  /* 黑体字体 */
                color: #000000;  /* 黑色文字 */
            }
            QLabel {
                color: #000000;  /* 黑色文字 */
                font-family: "Microsoft YaHei", "SimHei";  /* 黑体字体 */
            }
            QTextEdit {
                background-color: #FFFFFF;  /* 白色文本框背景 */
                color: #000000;  /* 黑色文字 */
                font-family: "Microsoft YaHei", "SimHei";  /* 黑体字体 */
                border: 1px solid #BBDEFB;
                border-radius: 5px;
                padding: 5px;
            }
            QPushButton {
                background-color: #BBDEFB;
                color: #000000;  /* 黑色文字 */
                font-family: "SimHei";  /* 黑体字体 */
                font-size: 16pt;
                border: 1px solid #90CAF9;
                border-radius: 5px;
                padding: 8px 20px;
                min-width: 80px;
            }
            QPushButton:hover {
                background-color: #90CAF9;
            }
            QPushButton:pressed {
                background-color: #64B5F6;
            }
        """)
        
        # 创建布局
        layout = QVBoxLayout()
        
        # 添加说明文本
        info_label = QLabel("请输入要包含的模块名（支持以下分隔符）：\n\n" +
                         "• 逗号分隔：numpy, pandas, requests\n" +
                         "• 分号分隔：numpy; pandas; requests\n" +
                         "• 换行分隔：\nnumpy\npandas\nrequests\n\n" +
                         "示例：\nnumpy,pandas\nrequests\nmatplotlib")
        info_label.setWordWrap(True)
        layout.addWidget(info_label)
        
        # 添加文本输入框
        text_edit = QTextEdit()
        text_edit.setPlaceholderText("在此输入模块名...")
        layout.addWidget(text_edit)
        
        # 添加按钮
        button_layout = QHBoxLayout()
        ok_button = NeumorphicButton("确定")
        cancel_button = NeumorphicButton("取消")
        button_layout.addWidget(ok_button)
        button_layout.addWidget(cancel_button)
        layout.addLayout(button_layout)
        
        dialog.setLayout(layout)
        
        # 连接按钮信号
        ok_button.clicked.connect(dialog.accept)
        cancel_button.clicked.connect(dialog.reject)
        
        # 显示对话框并获取结果
        result = dialog.exec()
        ok = (result == QDialog.Accepted)
        modules_text = text_edit.toPlainText() if ok else ""
        
        if ok and modules_text.strip():
            # 解析模块名（支持多种分隔符）
            modules = []
            lines = modules_text.strip().split('\n')
            for line in lines:
                # 先按逗号分割
                comma_parts = [part.strip() for part in line.split(',') if part.strip()]
                # 再按分号分割每个逗号分割的部分
                for part in comma_parts:
                    semicolon_parts = [p.strip() for p in part.split(';') if p.strip()]
                    modules.extend(semicolon_parts)
            
            # 去重并过滤空值
            modules = list(set(module for module in modules if module))
            
            if modules:
                # 显示将要添加的模块列表
                module_list = '\n'.join([f'• {module}' for module in modules[:10]])
                if len(modules) > 10:
                    module_list += f'\n... 还有 {len(modules) - 10} 个模块'
                
                # 创建确认对话框
                confirm_dialog = QDialog(self)
                confirm_dialog.setWindowTitle("确认添加")
                confirm_dialog.resize(450, 350)  # 设置初始尺寸，允许用户拖拽调整
                confirm_dialog.setMinimumSize(350, 250)  # 设置最小尺寸
                
                # 设置确认对话框样式
                confirm_dialog.setStyleSheet("""
                    QDialog {
                        background-color: #E3F2FD;  /* 天蓝色背景 */
                        font-family: "Microsoft YaHei", "SimHei";  /* 黑体字体 */
                        color: #000000;  /* 黑色文字 */
                    }
                    QLabel {
                        color: #000000;  /* 黑色文字 */
                        font-family: "Microsoft YaHei", "SimHei";  /* 黑体字体 */
                    }
                    QPushButton {
                        background-color: #BBDEFB;
                        color: #000000;  /* 黑色文字 */
                        font-family: "SimHei";  /* 黑体字体 */
                        font-size: 16pt;
                        border: 1px solid #90CAF9;
                        border-radius: 5px;
                        padding: 8px 20px;
                        min-width: 80px;
                    }
                    QPushButton:hover {
                        background-color: #90CAF9;
                    }
                    QPushButton:pressed {
                        background-color: #64B5F6;
                    }
                """)
                
                # 创建布局
                confirm_layout = QVBoxLayout()
                
                # 添加确认文本
                confirm_label = QLabel(f"将要添加以下 {len(modules)} 个模块：\n\n{module_list}\n\n确认添加吗？")
                confirm_label.setWordWrap(True)
                confirm_layout.addWidget(confirm_label)
                
                # 添加按钮
                button_layout = QHBoxLayout()
                yes_button = NeumorphicButton("是")
                no_button = NeumorphicButton("否")
                button_layout.addWidget(yes_button)
                button_layout.addWidget(no_button)
                confirm_layout.addLayout(button_layout)
                
                confirm_dialog.setLayout(confirm_layout)
                
                # 连接按钮信号
                yes_button.clicked.connect(confirm_dialog.accept)
                no_button.clicked.connect(confirm_dialog.reject)
                
                # 显示确认对话框
                confirm_result = confirm_dialog.exec()
                confirm = (confirm_result == QDialog.Accepted)
                
                if confirm:
                    # 批量添加模块
                    for module in modules:
                        self.deps_list.addItem(f"{self.MODULE_PREFIX}{module}")
                    # 强制刷新界面显示
                    self.deps_list.update()
                    self.deps_list.repaint()
                    self.log_message(f"✓ 已批量添加 {len(modules)} 个模块\n", "info")
            else:
                QMessageBox.warning(self, "警告", "未检测到有效的模块名")

    
    def add_resource(self):
        """添加资源文件
        
        该方法允许用户选择一个或多个资源文件，并指定其在打包后的程序中的目标路径。
        选中的资源文件会被添加到依赖列表中。
        """
        # 浏览并选择资源文件（支持多选）
        paths = self.browse_files(
            "选择要包含的资源文件",
            "All Files (*)"
        )
        
        # 如果选择了文件
        if paths:
            # 询问用户是否使用统一的目标路径前缀
            reply = QMessageBox.question(
                self,
                "目标路径设置",
                "是否为所有选中的文件使用统一的目标路径前缀？",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.Yes
            )
            
            if reply == QMessageBox.Yes:
                # 使用统一的前缀
                prefix, ok = QInputDialog.getText(
                    self,
                    "目标路径前缀",
                    "请输入目标路径前缀（如 'assets/'）：",
                    text="assets/"
                )
                
                if ok and prefix:
                    # 为每个文件添加依赖项
                    for path in paths:
                        filename = os.path.basename(path)
                        dest = f"{prefix}{filename}"
                        self.deps_list.addItem(f"{self.RESOURCE_PREFIX}{path} => {dest}")
                    # 强制刷新界面显示
                    self.deps_list.update()
                    self.deps_list.repaint()
            else:
                # 为每个文件单独设置目标路径
                for path in paths:
                    default_name = os.path.basename(path)
                    dest, ok = QInputDialog.getText(
                        self,
                        "目标路径",
                        f"资源文件 {default_name} 将复制到的位置:",
                        text=f"assets/{default_name}"
                    )
                    
                    if ok and dest:
                        self.deps_list.addItem(f"{self.RESOURCE_PREFIX}{path} => {dest}")
                # 强制刷新界面显示
                self.deps_list.update()
                self.deps_list.repaint()
    
    def remove_dependency(self):
        """移除选中的依赖项
        
        该方法用于从依赖列表中移除用户选中的项，支持批量删除。
        """
        # 获取所有选中的依赖项
        selected_items = self.deps_list.selectedItems()
        
        if not selected_items:
            QMessageBox.information(self, "提示", "请先选择要删除的依赖项")
            return
        
        # 询问用户确认删除
        if len(selected_items) == 1:
            # 单个文件删除
            reply = QMessageBox.question(
                self,
                "确认删除",
                f"确定要删除选中的依赖项吗？\n\n{selected_items[0].text()}",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No
            )
        else:
            # 多个文件删除
            item_names = [item.text() for item in selected_items]
            reply = QMessageBox.question(
                self,
                "确认删除",
                f"确定要删除选中的 {len(selected_items)} 个依赖项吗？\n\n" + "\n".join(item_names[:5]) + 
                ("\n..." if len(item_names) > 5 else ""),
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No
            )
        
        if reply == QMessageBox.Yes:
            # 遍历选中的项并从列表中移除（从后往前删除避免索引问题）
            for item in reversed(selected_items):
                row = self.deps_list.row(item)
                self.deps_list.takeItem(row)
            
            # 显示删除成功的提示
            self.log_message(f"✓ 已删除 {len(selected_items)} 个依赖项\n", "info")
    
    def select_all_dependencies(self):
        """全选/取消全选依赖项
        
        该方法用于选择或取消选择依赖列表中的所有项。
        如果当前所有项都已选中，则取消全选；否则全选所有项。
        """
        # 获取列表中的总项目数
        total_items = self.deps_list.count()
        
        if total_items == 0:
            QMessageBox.information(self, "提示", "依赖列表为空")
            return
        
        # 获取当前已选中的项目数
        selected_count = len(self.deps_list.selectedItems())
        
        # 如果所有项目都已选中，则取消全选；否则全选
        if selected_count == total_items:
            # 取消全选
            self.deps_list.clearSelection()
            self.log_message("✓ 已取消全选\n", "info")
        else:
            # 全选所有项目
            for i in range(total_items):
                item = self.deps_list.item(i)
                item.setSelected(True)
            self.log_message(f"✓ 已全选 {total_items} 个依赖项\n", "info")
      
      # ================= 打包核心方法 =================
    
    def build_nuitka_command(self):
        """构建Nuitka编译命令
        
        该方法负责构建完整的Nuitka编译命令行参数，包括:
        1. 验证输入参数（脚本路径、输出目录等）
        2. 设置Python解释器路径
        3. 根据用户界面设置构建编译选项
        4. 处理插件启用和冲突检测
        5. 添加资源文件和模块依赖
        6. 返回完整的命令行参数列表
        
        Returns:
            list: Nuitka编译命令行参数列表，如果验证失败则返回None
        """
        # 验证主脚本路径是否已选择
        script_path = self.script_entry.text().strip()
        # 标准化路径分隔符为正斜杠
        # 使用Windows系统默认的路径格式
        if not script_path:
            self.log_message("⛔ 错误：未选择主脚本\n", "error")
            return None
            
        # 验证主脚本文件是否存在
        if not os.path.exists(script_path):
            self.log_message(f"⛔ 错误：脚本文件不存在: {script_path}\n", "error")
            return None
        
        # 验证输出目录是否已设置
        output_dir = self.output_entry.text().strip()
        # 使用Windows系统默认的路径格式
        if not output_dir:
            self.log_message("⛔ 错误：未设置输出目录\n", "error")
            return None
            
        # 创建输出目录（如果不存在）
        if not os.path.exists(output_dir):
            try:
                os.makedirs(output_dir, exist_ok=True)
                self.log_message(f"✓ 已创建输出目录: {output_dir}\n", "info")
            except Exception as e:
                self.log_message(f"⛔ 创建输出目录失败: {str(e)}\n", "error")
                return None
        
        # 验证图标文件路径（如果已设置）
        icon_path = self.icon_entry.text().strip()
        if icon_path and not os.path.exists(icon_path):
            self.log_message(f"⚠ 警告：图标文件不存在: {icon_path}\n", "warning")
        
        # 获取Python解释器路径
        python_path = self.python_combo.currentText().strip()
        if not python_path:
            # 如果用户未选择Python解释器，使用当前运行的Python
            # 修复打包成exe后sys.executable指向exe本身的问题
            if getattr(sys, 'frozen', False):
                # 当前是打包后的exe，尝试从环境变量中获取Python路径
                python_path = os.environ.get('PYTHON_PATH', '')
                if not python_path or not os.path.exists(python_path):
                    # 如果环境变量中没有Python路径或路径不存在，使用默认Python
                    python_path = 'python'
            else:
                # 当前是Python脚本，使用sys.executable
                python_path = sys.executable
        elif not os.path.exists(python_path):
            self.log_message(f"⚠ 警告：指定的Python解释器不存在: {python_path}，将使用当前Python\n", "warning")
            if getattr(sys, 'frozen', False):
                # 当前是打包后的exe，尝试从环境变量中获取Python路径
                python_path = os.environ.get('PYTHON_PATH', '')
                if not python_path or not os.path.exists(python_path):
                    # 如果环境变量中没有Python路径或路径不存在，使用默认Python
                    python_path = 'python'
            else:
                # 当前是Python脚本，使用sys.executable
                python_path = sys.executable
        else:
            # 验证用户选择的Python解释器
            self.log_message(f"🔍 验证Python解释器: {python_path}\n", "info")
        
        # 根据优化级别构建基础命令
        if self.opt_var == 0:
            # 无优化
            cmd = [python_path, "-m", "nuitka"]
        elif self.opt_var == 1:
            # 基本优化
            cmd = [python_path, "-O", "-m", "nuitka"]
        else:  # level 2
            # 完全优化
            cmd = [python_path, "-OO", "-m", "nuitka"]
        
        # 添加自动下载确认参数，避免交互式询问
        cmd.append("--assume-yes-for-downloads")
       
        # 编译器选择（仅Windows平台有效）
        if self.compiler_var == "msvc":
            # 使用Microsoft Visual C++编译器
            cmd.append("--msvc=latest")
        elif self.compiler_var == "mingw":
            # 使用MinGW-w64编译器
            cmd.append("--mingw64")
        
        # 打包模式设置
        if self.mode_var == "onefile":
            # 单文件模式：将所有内容打包到一个可执行文件中
            cmd.append("--onefile")
            # cmd.append("--standalone")
            
        else:
            # 独立模式：生成包含所有依赖的文件夹
            cmd.append("--standalone")
        
        # 控制台设置（仅Windows平台有效）
        if self.console_var == "enable":
            # 强制启用控制台窗口
            cmd.append("--windows-console-mode=force")  # 强制显示控制台窗口（即使你是 GUI 程序）
            # cmd.append("--windows-console-mode=default")  # 使用默认控制台模式（根据程序类型自动选择，一般会显示控制台）
        else:
            # 隐藏控制台窗口
            cmd.append("--windows-console-mode=disable")  # 完全禁用控制台，适用于纯 GUI 程序（如 PySide6/PyQt 程序）
            # cmd.append("--windows-console-mode=hide")  # 隐藏控制台窗口（适用于 GUI 程序）
        # 输出目录配置
        output_dir = os.path.abspath(output_dir)
        cmd.append(f"--output-dir={output_dir}")
        
        # 可执行文件名称设置
        exe_name = self.name_entry.text().strip()
        if exe_name:
            # 确保文件名以.exe结尾
            if not exe_name.endswith(".exe"):
                exe_name += ".exe"
            # cmd.append(f"--output-filename={exe_name}")
            # 构建完整的输出路径
            cmd.append(f"--output-filename={os.path.join(exe_name)}")
        
        # 图标设置（如果已选择）
        if icon_path:
            # 使用Windows系统默认的路径格式
            icon_path = os.path.abspath(icon_path)
            # cmd.append(f"--windows-icon-from-ico={icon_path}")
            cmd.append(f"--windows-icon-from-ico={os.path.abspath(icon_path)}")
        
        # LTO链接优化设置
        if self.lto_var and self.lto_var != "off":
            # 根据用户选择的LTO等级添加相应参数
            cmd.append(f"--lto={self.lto_var}")

            
        # 并行任务数设置
        jobs = self.jobs_var
        cmd.append(f"--jobs={jobs}")
        # 启用多进程插件（根据用户设置）
        if self.multiprocessing_var:
            cmd.append("--enable-plugin=multiprocessing")        
        # 开启 Nuitka 的依赖追踪功能
        cmd.append("--follow-imports")
        # 开启 Nuitka 的依赖追踪功能，不推荐使用打包极慢，体积巨大，可能引入不必要的模块
        # cmd.append("--follow-import-to=*")
        # 开启显示操作的进度条或进度信息
        cmd.append("--show-progress")
        # 根据用户选择的调试选项添加相应参数
        if self.show_memory_cb.isChecked():
            # 显示内存占用
            cmd.append("--show-memory")
        # 显示编译时间，此命令已被移除
        # cmd.append("--show-times")
        if self.show_modules_cb.isChecked():
            # 显示被包含的模块列表
            cmd.append("--show-modules")
        if self.show_scons_cb.isChecked():
            # 显示scons构建过程
            cmd.append("--show-scons")
        if self.verbose_cb.isChecked():
            # 显示详细输出日志
            cmd.append("--verbose")
        # if self.show_progress_cb.isChecked():
        #     # 显示打包进度
        #     cmd.append("--show-progress")
        # 插件启用 - 处理冲突插件
        selected_plugins = []
        has_pyside6 = False
        has_pyqt5 = False
        
        # 遍历用户选择的插件列表
        for item in self.plugin_list.selectedItems():
            plugin_name = item.text()
            if plugin_name == "pyside6":
                has_pyside6 = True
                selected_plugins.append(plugin_name)
            elif plugin_name == "pyqt5":
                has_pyqt5 = True
                selected_plugins.append(plugin_name)
            else:
                selected_plugins.append(plugin_name)
        
        # 处理插件冲突：PySide6和PyQt5不能同时使用
        if has_pyside6 and has_pyqt5:
            self.log_message("⚠ 警告：检测到同时启用了PySide6和PyQt5插件，它们存在冲突。将只使用PySide6插件。\n", "warning")
            selected_plugins = [p for p in selected_plugins if p != "pyqt5"]
        
        # UPX压缩设置（如果启用且未在插件列表中选中）
        if self.upx_var and "upx" not in [item.text() for item in self.plugin_list.selectedItems()]:
            selected_plugins.append("upx")
        
        # 检查是否使用了tkinter模块，如果使用了且用户未选择tk-inter插件，则给出提示
        if self.uses_tkinter(script_path) and "tk-inter" not in selected_plugins:
            self.log_message("⚠ 警告：检测到脚本中使用了tkinter模块，但未选择tk-inter插件，可能导致运行时错误\n", "warning")
        
        # 检查是否使用了PySide6模块，如果使用了且用户未选择pyside6插件，则给出提示
        if self.uses_pyside6(script_path) and "pyside6" not in selected_plugins:
            self.log_message("⚠ 警告：检测到脚本中使用了PySide6模块，但未选择pyside6插件，可能导致运行时错误\n", "warning")
        
        # 检查是否使用了PyQt5模块，如果使用了且用户未选择pyqt5插件，则给出提示
        if self.uses_pyqt5(script_path) and "pyqt5" not in selected_plugins:
            self.log_message("⚠ 警告：检测到脚本中使用了PyQt5模块，但未选择pyqt5插件，可能导致运行时错误\n", "warning")
        
        # 检查是否使用了PIL模块，Nuitka不需要为PIL/Pillow专门启用插件
        if self.uses_pil(script_path) and "PIL" in selected_plugins:
            self.log_message("ℹ 提示：检测到脚本中使用了PIL/Pillow模块，Nuitka会自动处理其依赖，无需专门启用插件\n", "info")
        
        # 检查是否使用了numpy模块，如果使用了且用户未选择numpy插件，则给出提示
        if self.uses_numpy(script_path) and "numpy" not in selected_plugins:
            self.log_message("⚠ 警告：检测到脚本中使用了numpy模块，但未选择numpy插件，可能导致运行时错误\n", "warning")
        
        # 添加插件到命令
        for plugin_name in selected_plugins:
            # Nuitka中没有名为'PIL'的插件，使用PIL/Pillow不需要特殊插件
            if plugin_name == "PIL":
                self.log_message("ℹ 提示：Nuitka中没有名为'PIL'的插件，PIL/Pillow依赖会自动处理\n", "info")
                continue
            elif plugin_name == "upx":
                # 启用UPX压缩插件
                cmd.append("--plugin-enable=upx")
                # 当使用onefile模式时，添加--onefile-no-compression参数以避免双重压缩
                if self.mode_var == "onefile":
                    cmd.append("--onefile-no-compression")
                    self.log_message("✓ 已自动添加--onefile-no-compression参数以避免双重压缩\n", "success")
            else:
                # 启用其他插件
                cmd.append(f"--enable-plugin={plugin_name}")
                
                # 如果选择了pyside6插件，自动包含shiboken6模块
                if plugin_name == "pyside6":
                    # cmd.append("--include-package=shiboken6")
                    # cmd.append("--include-package=PySide6")
                    self.log_message("ℹ 提示：已自动包含shiboken6模块以支持PySide6\n", "info")

        # 处理资源文件和模块依赖
        for i in range(self.deps_list.count()):
            item = self.deps_list.item(i)
            # 处理资源文件
            if item.text().startswith(self.RESOURCE_PREFIX):
                parts = item.text()[len(self.RESOURCE_PREFIX):].split(" => ")
                if len(parts) == 2:
                    src, dest = parts
                    # 使用Windows系统默认的路径格式
                    # 添加数据文件到打包目录
                    cmd.append(f"--include-data-files={src}={dest}")
            # 处理额外模块
            elif item.text().startswith(self.MODULE_PREFIX):
                module = item.text()[len(self.MODULE_PREFIX):]
                # 使用Windows系统默认的路径格式
                # 显式包含指定模块
                cmd.append(f"--include-module={module}")
        
        # 添加主脚本路径到命令行
        script_path = os.path.abspath(script_path)
        cmd.append(script_path)
        
        # 根据用户设置决定是否清理中间文件
        if self.cleanup_cache:
            # 启用编译后自动清理临时文件
            cmd.append("--remove-output")
        else:
            # 禁用自动清理，保留缓存文件以加快下次编译
            self.log_message("⚠ 已禁用临时文件清理，请注意缓存管理\n", "warning")
        
        return cmd
    
    def manual_cleanup_cache(self):
        """手动清理缓存的用户界面入口
        
        提供用户友好的界面来手动清理build缓存
        """
        # 检查输出目录
        output_dir = self.output_entry.text()
        if not output_dir:
            QMessageBox.warning(self, "警告", "请先设置输出目录")
            return
        
        # 确认对话框
        reply = QMessageBox.question(
            self,
            "确认清理",
            "确定要手动清理build缓存文件夹吗？\n这将删除所有编译过程中产生的临时文件和build文件夹。",
            QMessageBox.Yes | QMessageBox.No
        )
        
        if reply == QMessageBox.Yes:
            self.log_message("\n=== 开始手动清理缓存 ===\n", "info")
            self._manual_cleanup_build_cache()
            self.log_message("\n=== 手动清理缓存完成 ===\n", "info")
            QMessageBox.information(self, "清理完成", "手动清理缓存操作已完成")
    
    def _manual_cleanup_build_cache(self):
        """手动清理build缓存文件夹
        
        在Nuitka的--remove-output参数可能失败的情况下，手动删除build文件夹
        """
        import shutil
        import glob
        
        try:
            # 获取输出目录
            output_text = self.output_entry.text()
            # 使用Windows系统默认的路径格式
            output_dir = os.path.abspath(output_text)
            
            # 查找可能的build文件夹和打包产物
            # 1. 查找以.build为后缀的文件夹
            build_patterns = [
                # 标准构建文件夹
                os.path.join(output_dir, "*.build"),
                os.path.join(output_dir, "*.build-*"),
                os.path.join(output_dir, "build"),
                os.path.join(output_dir, "build-*"),
                
                # dist文件夹和构建产物
                os.path.join(output_dir, "*.dist"),
                os.path.join(output_dir, "*.dist-*"),
                # os.path.join(output_dir, "dist"),
                # os.path.join(output_dir, "dist-*"),
                
                # 单文件构建产物
                os.path.join(output_dir, ".onefile-build"),
                os.path.join(output_dir, ".onefile-build-*"),
                os.path.join(output_dir, "*.onefile-build"),
                os.path.join(output_dir, "*.onefile-build-*"),
                
                
                # 也检查当前目录下的构建文件夹
                os.path.join(os.path.dirname(output_dir), "*.build"),
                os.path.join(os.path.dirname(output_dir), "*.build-*"),
                os.path.join(os.path.dirname(output_dir), "build"),
                os.path.join(os.path.dirname(output_dir), "build-*"),
                os.path.join(os.path.dirname(output_dir), "*.dist"),
                os.path.join(os.path.dirname(output_dir), "*.dist-*"),
                # os.path.join(os.path.dirname(output_dir), "dist"),
                # os.path.join(os.path.dirname(output_dir), "dist-*"),
                os.path.join(os.path.dirname(output_dir), "*.onefile-build"),
                os.path.join(os.path.dirname(output_dir), "*.onefile-build-*"),
            ]
            
            cleaned_count = 0
            
            for pattern in build_patterns:
                build_dirs = glob.glob(pattern)
                for build_dir in build_dirs:
                    if os.path.exists(build_dir) and os.path.isdir(build_dir):
                        try:
                            self.log_message(f"🧹 正在手动清理build文件夹: {build_dir}\n", "info")
                            shutil.rmtree(build_dir)
                            self.log_message(f"✅ 成功清理build文件夹: {build_dir}\n", "success")
                            cleaned_count += 1
                        except PermissionError as e:
                            self.log_message(f"⚠ 清理build文件夹失败（权限不足）: {build_dir} - {e}\n", "warning")
                        except OSError as e:
                            self.log_message(f"⚠ 清理build文件夹失败（系统错误）: {build_dir} - {e}\n", "warning")
                        except Exception as e:
                            self.log_message(f"⚠ 清理build文件夹失败（未知错误）: {build_dir} - {e}\n", "warning")
            
            # 查找并清理单文件编译产生的临时文件
            temp_patterns = [
                os.path.join(output_dir, "*.c"),
                os.path.join(output_dir, "*.cpp"),
                os.path.join(output_dir, "*.h"),
                os.path.join(output_dir, "*.o"),
                os.path.join(output_dir, "*.obj"),
                os.path.join(output_dir, "*.manifest"),
                os.path.join(output_dir, "*.lib"),
                os.path.join(output_dir, "*.exp"),
                # 也检查当前目录下的临时文件
                os.path.join(os.path.dirname(output_dir), "*.c"),
                os.path.join(os.path.dirname(output_dir), "*.cpp"),
                os.path.join(os.path.dirname(output_dir), "*.h"),
                os.path.join(os.path.dirname(output_dir), "*.o"),
                os.path.join(os.path.dirname(output_dir), "*.obj"),
                os.path.join(os.path.dirname(output_dir), "*.manifest"),
                os.path.join(os.path.dirname(output_dir), "*.lib"),
                os.path.join(os.path.dirname(output_dir), "*.exp")
            ]
            
            temp_files_count = 0
            
            for pattern in temp_patterns:
                temp_files = glob.glob(pattern)
                for temp_file in temp_files:
                    if os.path.exists(temp_file) and os.path.isfile(temp_file):
                        try:
                            self.log_message(f"🧹 正在清理临时文件: {temp_file}\n", "info")
                            os.remove(temp_file)
                            self.log_message(f"✅ 成功清理临时文件: {temp_file}\n", "success")
                            temp_files_count += 1
                        except PermissionError as e:
                            self.log_message(f"⚠ 清理临时文件失败（权限不足）: {temp_file} - {e}\n", "warning")
                        except OSError as e:
                            self.log_message(f"⚠ 清理临时文件失败（系统错误）: {temp_file} - {e}\n", "warning")
                        except Exception as e:
                            self.log_message(f"⚠ 清理临时文件失败（未知错误）: {temp_file} - {e}\n", "warning")
            
            if cleaned_count > 0 or temp_files_count > 0:
                self.log_message(f"🎉 手动清理完成: 清理了 {cleaned_count} 个build文件夹和 {temp_files_count} 个临时文件\n", "success")
            else:
                self.log_message("ℹ 未发现需要清理的build文件夹或临时文件\n", "info")
                
        except Exception as e:
            self.log_message(f"⛔ 手动清理缓存过程中发生错误: {e}\n", "error")
    
    def quick_cleanup_all_builds(self):
        """快速清理所有构建产物
        
        一键清理当前目录下的所有Nuitka构建产物，包括：
        - .build文件夹
        - .dist文件夹  
        - .onefile-build文件夹
        - 临时构建文件
        """
        import shutil
        import glob
        
        try:
            current_dir = os.path.dirname(os.path.abspath(__file__))
            self.log_message(f"🚀 开始快速清理当前目录下的所有构建产物: {current_dir}\n", "info")
            
            # 清理模式列表
            cleanup_patterns = [
                # 构建文件夹
                os.path.join(current_dir, "*.build"),
                os.path.join(current_dir, "*.build-*"),
                os.path.join(current_dir, "build"),
                os.path.join(current_dir, "build-*"),
                
                # dist文件夹
                os.path.join(current_dir, "*.dist"),
                os.path.join(current_dir, "*.dist-*"),
                # os.path.join(current_dir, "dist"),
                # os.path.join(current_dir, "dist-*"),
                
                # 单文件构建
                os.path.join(current_dir, "*.onefile-build"),
                os.path.join(current_dir, "*.onefile-build-*"),
                os.path.join(current_dir, ".onefile-build"),
                os.path.join(current_dir, ".onefile-build-*"),
                

                
                # 临时文件
                os.path.join(current_dir, "*.c"),
                os.path.join(current_dir, "*.cpp"),
                os.path.join(current_dir, "*.h"),
                os.path.join(current_dir, "*.o"),
                os.path.join(current_dir, "*.obj"),
                os.path.join(current_dir, "*.manifest"),
                os.path.join(current_dir, "*.lib"),
                os.path.join(current_dir, "*.exp"),
                os.path.join(current_dir, "*.pdb")
            ]
            
            total_cleaned = 0
            
            for pattern in cleanup_patterns:
                items = glob.glob(pattern)
                for item in items:
                    if os.path.exists(item):
                        try:
                            if os.path.isdir(item):
                                self.log_message(f"🧹 正在清理文件夹: {os.path.basename(item)}\n", "info")
                                shutil.rmtree(item)
                                self.log_message(f"✅ 成功清理文件夹: {os.path.basename(item)}\n", "success")
                            else:
                                self.log_message(f"🧹 正在清理文件: {os.path.basename(item)}\n", "info")
                                os.remove(item)
                                self.log_message(f"✅ 成功清理文件: {os.path.basename(item)}\n", "success")
                            total_cleaned += 1
                        except Exception as e:
                            self.log_message(f"⚠ 清理失败: {os.path.basename(item)} - {e}\n", "warning")
            
            if total_cleaned > 0:
                self.log_message(f"🎉 快速清理完成！共清理了 {total_cleaned} 个构建产物\n", "success")
            else:
                self.log_message("ℹ 当前目录下未发现需要清理的构建产物\n", "info")
                
        except Exception as e:
            self.log_message(f"⛔ 快速清理过程中发生错误: {e}\n", "error")
    
    def escape_powershell_arg(self, arg):
        """转义PowerShell命令行参数，正确处理包含空格和特殊字符的路径"""
        # 如果参数中包含空格或特殊字符，使用双引号包围
        if ' ' in arg or '\\' in arg or '"' in arg or "'" in arg:
            # 先替换参数中的双引号为两个双引号（PowerShell转义规则）
            escaped_arg = arg.replace('"', '""')
            # 再用双引号包围整个参数
            return f'"{escaped_arg}"'
        # 不包含特殊字符的参数直接返回
        return arg
    
    def run_nuitka(self):
        self.running = True
        self.message_queue.put(("log", "\n=== 开始打包 ===\n"))
        self.message_queue.put(("progress", 0))
        
        # 初始化更精确的进度跟踪变量
        start_time = time.time()
        total_files_processed = 0
        estimated_total_files = 0
        stage_progress = {
            'initialization': 0,      # 0-5%
            'dependency_analysis': 0,  # 5-15%
            'module_compilation': 0,  # 15-40%
            'code_generation': 0,     # 40-60%
            'c_compilation': 0,       # 60-75%
            'c_linking': 0,          # 75-90%
            'final_linking': 0,       # 90-98%
            'completion': 0           # 98-100%
        }
        current_stage = 'initialization'
        compilation_units = []
        linking_files = 0
        
        try:
            cmd = self.build_nuitka_command()
            if cmd is None:
                self.message_queue.put(("running", False))
                return
                
            self.message_queue.put(("log", f"执行命令: {' '.join(cmd)}\n"))
            
            # 在日志中明确提示将自动确认下载
            self.message_queue.put(("log", "✅ 已启用自动下载确认 (--assume-yes-for-downloads)\n", "info"))
            
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            env = os.environ.copy()
            upx_path = self.upx_path_entry.text().strip()
            if upx_path:
                upx_dir = os.path.dirname(upx_path)
                env["PATH"] = f"{upx_dir}{os.pathsep}{env['PATH']}"
                self.message_queue.put(("log", f"ℹ 已添加临时PATH: {upx_dir}\n"))
            
            # 获取用户选择的Python解释器路径
            python_cmd = self.python_combo.currentText().strip() if self.python_combo.currentText().strip() else sys.executable
            self.message_queue.put(("log", f"🔧 使用Python解释器: {python_cmd}\n"))
            
            # 为用户选择的Python解释器添加必要的环境变量支持
            # 确保Python解释器所在目录和Scripts目录在PATH中
            python_dir = os.path.dirname(python_cmd)
            scripts_dir = os.path.join(python_dir, 'Scripts') if platform.system() == "Windows" else os.path.join(python_dir, 'bin')
            
            # 临时修改环境变量PATH，确保Python解释器和其Scripts目录在PATH中
            if python_dir not in env["PATH"]:
                env["PATH"] = f"{python_dir}{os.pathsep}{env['PATH']}"
                self.message_queue.put(("log", f"ℹ 已临时添加Python解释器目录到PATH: {python_dir}\n"))
            
            if os.path.exists(scripts_dir) and scripts_dir not in env["PATH"]:
                env["PATH"] = f"{scripts_dir}{os.pathsep}{env['PATH']}"
                self.message_queue.put(("log", f"ℹ 已临时添加Scripts目录到PATH: {scripts_dir}\n"))
            
            # 检查是否为conda环境
            conda_env_name = self._get_conda_env_name(python_cmd)
            
            # 使用subprocess执行命令，Windows系统下使用shell=True
            if conda_env_name:
                # 如果是conda环境，先激活环境再执行命令
                activate_cmd = f'conda activate {conda_env_name} && '
                
                # 添加功能：在执行打包命令前，先查询该环境安装的库明细
                list_cmd = activate_cmd + 'conda list'
                self.message_queue.put(("log", f"🔍 查询conda环境 {conda_env_name} 的库明细...\n"))
                self.message_queue.put(("log", f"📋 执行命令: {list_cmd}\n"))
                
                try:
                    # 执行conda list命令
                    list_proc = subprocess.Popen(
                        list_cmd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                        text=True,
                        bufsize=1,
                        universal_newlines=True,
                        startupinfo=startupinfo,
                        shell=True
                    )
                    
                    # 输出conda list的结果
                    line_count = 0
                    for line in list_proc.stdout:
                        self.message_queue.put(("log", f"{line}"))
                        line_count += 1
                    
                    list_proc.wait()
                    self.message_queue.put(("log", f"✅ conda list命令执行完成，共输出 {line_count} 行\n"))
                    
                except Exception as e:
                    self.message_queue.put(("log", f"⚠ conda list命令执行失败: {str(e)}\n"))
                
                # 执行原始的打包命令
                full_cmd = activate_cmd + ' '.join([self.escape_powershell_arg(arg) for arg in cmd])
                self.message_queue.put(("log", f"🚀 激活conda环境: {conda_env_name}\n"))
                self.message_queue.put(("log", f"📋 执行完整命令: {full_cmd}\n"))
                self.proc = subprocess.Popen(
                    full_cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    startupinfo=startupinfo,
                    env=env,
                    shell=True
                )
            else:
                # Windows系统下使用shell=True执行命令
                cmd_str = ' '.join([self.escape_powershell_arg(arg) for arg in cmd])
                self.message_queue.put(("log", f"📋 执行命令: {cmd_str}\n"))
                self.proc = subprocess.Popen(
                    cmd_str,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    startupinfo=startupinfo,
                    env=env,
                    shell=True
                )
            
            progress = 0
            last_progress = 0
            timeout_counter = 0
            stuck_at_99_counter = 0  # 新增：记录在99%卡住的次数
            stage_progress = 0  # 初始化阶段进度
            current_stage = 'initialization'  # 初始化当前阶段
            total_files_processed = 0  # 初始化文件处理计数
            compilation_units = []  # 初始化编译单元列表
            estimated_total_files = 0  # 初始化估算总文件数
            c_linking_total_files = 0  # C链接阶段总文件数
            c_linking_processed_files = 0  # C链接阶段已处理文件数
            
            for line in self.proc.stdout:
                if not self.running:
                    break
                    
                self.message_queue.put(("log", line))
                
                # 增强的进度匹配和阶段检测
                match = self.PROGRESS_PATTERN.search(line)
                if match:
                    progress = int(match.group(1))
                    self.message_queue.put(("progress", progress))
                    last_progress = progress
                    timeout_counter = 0
                    stuck_at_99_counter = 0  # 重置99%卡住计数器
                else:
                    # 检测各个编译阶段
                    if "Analyzing dependencies" in line or "Dependency analysis" in line:
                        current_stage = 'dependency_analysis'
                        progress = self.calculate_stage_progress(stage_progress, current_stage, 10)
                        # 确保进度不会倒退
                        if progress > last_progress:
                            self.message_queue.put(("progress", progress))
                            last_progress = progress
                        self.message_queue.put(("log", "\n🔍 正在分析项目依赖关系...\n", "info"))
                    
                    elif "Compiling" in line and "module" in line.lower():
                        current_stage = 'module_compilation'
                        total_files_processed += 1
                        progress = self.calculate_stage_progress(stage_progress, current_stage, 25, total_files_processed)
                        # 确保进度不会倒退
                        if progress > last_progress:
                            self.message_queue.put(("progress", progress))
                            last_progress = progress
                    
                    elif "Generating C code" in line or "Code generation" in line:
                        current_stage = 'code_generation'
                        progress = self.calculate_stage_progress(stage_progress, current_stage, 50)
                        # 确保进度不会倒退
                        if progress > last_progress:
                            self.message_queue.put(("progress", progress))
                            last_progress = progress
                        self.message_queue.put(("log", "\n⚡ 正在生成C代码...\n", "info"))
                    
                    elif "Nuitka-Scons:" in line and "compiling" in line:
                        current_stage = 'c_compilation'
                        total_files_processed += 1
                        progress = self.calculate_stage_progress(stage_progress, current_stage, 70, total_files_processed)
                        # 确保进度不会倒退
                        if progress > last_progress:
                            self.message_queue.put(("progress", progress))
                            last_progress = progress
                    
                    elif c_linking_match := self.C_LINKING_PATTERN.search(line):
                        current_stage = 'c_linking'
                        c_linking_total_files = int(c_linking_match.group(1))
                        c_linking_processed_files = 0  # 重置已处理文件计数
                        progress = self.calculate_stage_progress(stage_progress, current_stage, 75, c_linking_processed_files)
                        # 确保进度不会倒退
                        if progress > last_progress:
                            self.message_queue.put(("progress", progress))
                            last_progress = progress
                        self.message_queue.put(("log", f"\n🔧 进入C链接阶段，正在处理{c_linking_total_files}个编译文件...\n", "info"))
                        timeout_counter = 0
                        stuck_at_99_counter = 0
                    
                    elif linking_match := self.LINKING_PATTERN.search(line):
                        current_stage = 'final_linking'
                        progress = self.calculate_stage_progress(stage_progress, current_stage, 95)
                        # 确保进度不会倒退
                        if progress > last_progress:
                            self.message_queue.put(("progress", progress))
                            last_progress = progress
                        self.message_queue.put(("log", "\n🔗 正在进行最终链接操作...\n", "info"))
                        timeout_counter = 0
                    
                    elif "Done." in line or "Successfully created" in line:
                        current_stage = 'completion'
                        progress = 100
                        self.message_queue.put(("progress", progress))
                    
                    # 检测编译单元和文件数量
                    elif "Compilation unit" in line:
                        compilation_units.append(line.strip())
                        if not estimated_total_files:
                            estimated_total_files = len(compilation_units) * 2  # 估算总文件数
                    
                    # 检测C链接阶段的具体编译进度
                    elif current_stage == 'c_linking' and c_linking_total_files > 0:
                        # 检测各种编译完成模式
                        if ("creating " in line and (".o" in line or ".obj" in line)) or \
                           ("compiling " in line.lower() and (".c" in line or ".cpp" in line)) or \
                           ("linking " in line.lower()) or \
                           ("building " in line.lower() and ("object" in line or "library" in line)):
                            c_linking_processed_files += 1
                            # 根据已处理文件数计算进度
                            progress = self.calculate_stage_progress(stage_progress, current_stage, 75, c_linking_processed_files)
                            # 确保进度不会倒退
                            if progress > last_progress:
                                self.message_queue.put(("progress", progress))
                                last_progress = progress
                            # 每处理10个文件显示一次进度
                            if c_linking_processed_files % 10 == 0 or c_linking_processed_files == c_linking_total_files:
                                self.message_queue.put(("log", f"📊 C链接进度: {c_linking_processed_files}/{c_linking_total_files} ({progress:.0f}%)\n", "info"))
                            timeout_counter = 0
                    
                    else:
                        timeout_counter += 1
                        # 3秒没有更新进度则缓慢前进
                        if timeout_counter >= 30:  # 约3秒
                            # 如果已经在99%，不要无限增加
                            if last_progress >= 99:
                                stuck_at_99_counter += 1
                                # 在99%卡住超过30秒，显示提示信息
                                if stuck_at_99_counter == 10:  # 约30秒
                                    elapsed_time = time.time() - start_time
                                    self.message_queue.put(("log", f"\n📝 正在进行最终处理和优化 (已用时: {elapsed_time:.1f}秒)...\n", "info"))
                                # 在99%卡住超过60秒，显示更详细的提示
                                elif stuck_at_99_counter == 20:  # 约60秒
                                    elapsed_time = time.time() - start_time
                                    remaining_time = self.estimate_remaining_time(start_time, last_progress)
                                    self.message_queue.put(("log", f"💡 提示：Nuitka正在进行链接和优化操作，预计剩余时间: {remaining_time}\n", "info"))
                            else:
                                progress = min(99, last_progress + 1)
                                self.message_queue.put(("progress", progress))
                                last_progress = progress
                            timeout_counter = 0
            
            return_code = self.proc.wait()
            
            if return_code == 0 and self.running:
                total_time = time.time() - start_time
                self.message_queue.put(("progress", 100))
                self.message_queue.put(("log", "\n" + "="*30))
                self.message_queue.put(("log", f"🎉 打包成功! 可执行文件已生成 (总用时: {total_time:.1f}秒)\n", "success"))
                self.message_queue.put(("log", "="*30 + "\n"))
                
                # 显示成功信息
                output_dir = self.output_entry.text()
                # 使用Windows系统默认的路径格式
                self.message_queue.put(("log", f"输出目录: {os.path.abspath(output_dir)}\n", "info"))
            elif self.running:
                total_time = time.time() - start_time
                self.message_queue.put(("progress", 100))
                self.message_queue.put(("log", "\n" + "="*30))
                self.message_queue.put(("log", f"!!! 打包失败 (代码:{return_code}, 总用时: {total_time:.1f}秒) !!!\n", "error"))
                self.message_queue.put(("log", "="*30 + "\n"))
        
        except FileNotFoundError as e:
            self.message_queue.put(("log", f"⛔ 文件不存在错误: {str(e)}\n", "error"))
        except PermissionError as e:
            self.message_queue.put(("log", f"⛔ 权限错误: {str(e)}\n", "error"))
        except OSError as e:
            self.message_queue.put(("log", f"⛔ 系统错误: {str(e)}\n", "error"))
        except CalledProcessError as e:
            self.message_queue.put(("log", f"⛔ 子进程执行错误: {str(e)}\n", "error"))
        except Exception as e:
            self.message_queue.put(("log", f"⛔ 未知错误: {str(e)}\n", "error"))
        
        finally:
            # 如果启用了清理缓存且打包成功，尝试手动清理build文件夹
            if self.cleanup_cache and return_code == 0:
                self._manual_cleanup_build_cache()
            
            self.message_queue.put(("running", False))
            self.running = False
            self.message_queue.put(("enable_button", True))
    
    def calculate_stage_progress(self, stage_progress, current_stage, base_progress, file_count=0):
        """根据当前阶段和文件数量计算更精确的进度"""
        stage_ranges = {
            'initialization': (0, 5),
            'dependency_analysis': (5, 15),
            'module_compilation': (15, 40),
            'code_generation': (40, 60),
            'c_compilation': (60, 75),
            'c_linking': (75, 90),
            'final_linking': (90, 98),
            'completion': (98, 100)
        }
        
        min_progress, max_progress = stage_ranges.get(current_stage, (0, 100))
        
        # 确保基础进度至少在阶段范围内
        if base_progress < min_progress:
            base_progress = min_progress
        elif base_progress > max_progress:
            base_progress = max_progress
        
        if current_stage in ['module_compilation', 'c_compilation', 'c_linking'] and file_count > 0:
            # 对于有文件计数的阶段，根据文件数量计算进度
            progress_range = max_progress - min_progress
            
            # 根据不同阶段使用不同的文件数量估算
            if current_stage == 'c_linking':
                # C链接阶段：根据实际文件数量计算进度
                # 假设总文件数为c_linking_total_files，但我们不知道具体值，所以使用file_count作为进度指示
                # 这里我们假设每个文件代表一定的进度增量
                if hasattr(self, 'c_linking_total_files') and self.c_linking_total_files > 0:
                    # 如果知道总文件数，使用精确计算
                    file_progress = min(file_count / self.c_linking_total_files, 1.0) * progress_range
                else:
                    # 如果不知道总文件数，使用估算（假设平均处理100个文件）
                    file_progress = min(file_count / 100.0, 1.0) * progress_range
            else:
                # 其他阶段：使用原有的估算逻辑
                file_progress = min(file_count / 50.0, 1.0) * progress_range
            
            calculated_progress = min_progress + file_progress
            # 确保进度在合理范围内
            return max(min_progress, min(max_progress, calculated_progress))
        else:
            # 对于其他阶段，返回基础进度，确保不为0（除非是初始化阶段）
            if current_stage == 'initialization':
                return max(0, base_progress)
            else:
                return max(min_progress, base_progress)
    
    def estimate_remaining_time(self, start_time, current_progress):
        """估算剩余时间"""
        if current_progress <= 0:
            return "估算中..."
        
        elapsed_time = time.time() - start_time
        if elapsed_time <= 0:
            return "估算中..."
        
        # 计算每1%所需的平均时间
        time_per_percent = elapsed_time / current_progress
        remaining_progress = 100 - current_progress
        estimated_remaining = time_per_percent * remaining_progress
        
        if estimated_remaining < 60:
            return f"约{estimated_remaining:.0f}秒"
        elif estimated_remaining < 3600:
            return f"约{estimated_remaining/60:.1f}分钟"
        else:
            return f"约{estimated_remaining/3600:.1f}小时"
    
    def start_packaging(self):
        if self.running:
            return
            
        if not self.script_entry.text():
            QMessageBox.warning(self, "警告", "请选择主脚本文件")
            return
            
        if not self.output_entry.text():
            QMessageBox.warning(self, "警告", "请设置输出目录")
            return
            
        # 记录用户操作
        script_path = self.script_entry.text().strip()
        output_dir = self.output_entry.text().strip()
        app_name = self.name_entry.text().strip()
        
        self.log_user_action("开始打包", f"脚本: {script_path}")
        self.log_user_action("打包配置", f"输出目录: {output_dir}, 应用名称: {app_name}")
            
        # 检查UPX设置
        upx_selected = any(item.text() == "upx" for item in self.plugin_list.selectedItems())
        if upx_selected and not self.is_upx_in_path() and not self.upx_path_entry.text():
            reply = QMessageBox.question(
                self,
                "警告",
                "UPX未在系统PATH中检测到，可能无法压缩。继续吗？",
                QMessageBox.Yes | QMessageBox.No
            )
            if reply != QMessageBox.Yes:
                # 记录用户操作
                self.log_user_action("取消打包", "UPX未配置，用户选择取消")
                return
        
        self.start_button.setEnabled(False)
        self.stop_button.setEnabled(True)
        self.export_button.setEnabled(True)
        
        # 显示打包开始状态
        self.log_message("🚀 开始打包进程...\n", "info")
        
        # 重置进度条状态
        self.progress.setValue(0)
        self.progress.setFormat("%p% - 开始打包...")
        
        # 记录打包开始
        self.log_user_action("启动打包进程", "开始后台Nuitka打包")
        threading.Thread(target=self.run_nuitka, daemon=True).start()
    
    def stop_packaging(self):
        if self.running:
            # 记录用户操作
            self.log_user_action("停止打包", "用户手动终止打包进程")
            
            self.running = False
            try:
                # 安全终止三步走
                if self.proc.poll() is None:  # 检查是否仍在运行
                    self.log_message("\n🛑 尝试终止打包进程...\n", "warning")
                    
                    # 第一步: 发送终止信号
                    self.proc.terminate()
                    
                    # 第二步: 等待5秒
                    try:
                        return_code = self.proc.wait(timeout=5)
                        if return_code is not None:
                            self.log_message(f"↪ 进程已终止 (退出码: {return_code})\n", "info")
                            # 记录用户操作
                            self.log_user_action("打包进程终止", f"退出码: {return_code}")
                    except TimeoutExpired:
                        # 第三步: 强制杀死进程
                        self.log_message("⚠ 超时未响应，强制结束进程...\n", "warning")
                        self.proc.kill()
                        self.log_message("⛔ 进程已被强制结束\n", "error")
                        # 记录用户操作
                        self.log_user_action("打包进程强制终止", "用户手动强制结束")
            except Exception as e:
                self.log_message(f"⛔ 终止进程时出错: {str(e)}\n", "error")
                # 记录用户操作
                self.log_user_action("终止打包出错", f"错误: {str(e)}")
            finally:
                self.start_button.setEnabled(True)
                self.stop_button.setEnabled(False)
                self.export_button.setEnabled(True)
                
                # 重置进度条状态
                self.progress.setValue(0)
                self.progress.setFormat("%p% - 已停止")
                
                # 记录用户操作
                self.log_user_action("打包已停止", "用户停止打包进程完成")
    
    # ================= UI 更新方法 =================
    
    def check_queue(self):
        try:
            while not self.message_queue.empty():
                msg = self.message_queue.get_nowait()
                msg_type = msg[0]
                
                if msg_type == "log":
                    text = msg[1]
                    if len(msg) > 2:
                        tag = msg[2]
                        self.log_message(text, tag)
                    else:
                        self.log_message(text)
                    
                elif msg_type == "progress":
                    progress_value = msg[1]
                    # 防止进度突然变为0（除非是初始化状态）
                    if progress_value == 0 and self.running:
                        # 如果正在运行中，进度不应该为0，保持上一次的进度
                        progress_value = self.progress.value()
                    
                    self.progress.setValue(progress_value)
                    
                    # 根据进度值更新状态文本，提供更精确的阶段信息
                    if progress_value == 0:
                        status_text = "准备就绪"
                    elif progress_value < 5:
                        status_text = "正在初始化..."
                    elif progress_value < 15:
                        status_text = "🔍 正在分析项目依赖关系..."
                    elif progress_value < 40:
                        status_text = f"📦 正在编译模块 ({progress_value:.0f}%)..."
                    elif progress_value < 60:
                        status_text = "⚡ 正在生成C代码..."
                    elif progress_value < 75:
                        status_text = f"🔨 正在编译C代码 ({progress_value:.0f}%)..."
                    elif progress_value < 90:
                        status_text = f"🔧 C链接处理中 ({progress_value:.0f}%)..."
                    elif progress_value < 98:
                        status_text = "🔗 最终链接中..."
                    elif progress_value < 100:
                        status_text = "📋 正在完成打包..."
                    else:  # 100%
                        status_text = "✅ 打包完成"
                    
                    self.progress.setFormat(f"%p% - {status_text}")
                    
                elif msg_type == "enable_button":
                    self.start_button.setEnabled(True)
                    self.stop_button.setEnabled(False)
                    self.export_button.setEnabled(True)
                    
                elif msg_type == "running":
                    self.running = msg[1]
        
        except queue.Empty:
            pass
    

    def _initialize_scroll_position(self):
        """初始化滚动条位置
        
        在窗口完全显示后调用此方法，确保滚动条位置正确设置，
        强制滚动到底部并设置auto_scroll为True，解决程序启动时
        默认不自动刷新日志的问题。
        """
        # 强制滚动到底部
        scrollbar = self.log_text.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())
        # 确保自动滚动状态为True
        self.auto_scroll = True
    
    def on_scroll_changed(self, value):
        """处理滚动条值变化事件"""
        # 获取滚动条的最大值
        max_value = self.log_text.verticalScrollBar().maximum()
        # 如果用户手动向上滚动（距离底部超过一定阈值），暂停自动滚动
        # 只有当用户明确向上滚动时才暂停，默认保持自动滚动
        if max_value > 0 and value < max_value - 5:  # 留5个像素的容差
            self.auto_scroll = False
        # 当滚动到底部时恢复自动滚动
        elif value >= max_value - 5:
            self.auto_scroll = True
    
    def on_log_double_click(self, event):
        """处理日志区域双击事件"""
        # 双击恢复自动滚动
        self.auto_scroll = True
        # 滚动到最底部
        cursor = self.log_text.textCursor()
        cursor.movePosition(QTextCursor.End)
        self.log_text.setTextCursor(cursor)
        self.log_text.ensureCursorVisible()
        # 调用原始的双击事件处理
        QTextEdit.mouseDoubleClickEvent(self.log_text, event)
    
    def _init_logging(self):
        """初始化日志记录功能"""
        try:
            # 创建日志目录
            os.makedirs(self.log_dir, exist_ok=True)
            
            # 获取当前Python路径
            current_python = self.python_combo.currentText().strip() if hasattr(self, 'python_combo') else sys.executable
            
            # 生成日志文件名（基于时间戳和Python路径）
            import hashlib
            python_hash = hashlib.md5(current_python.encode('utf-8')).hexdigest()[:8]
            timestamp = time.strftime("%Y%m%d_%H%M%S")
            log_filename = f"nuitka_log_{timestamp}_{python_hash}.log"
            
            # 设置日志文件路径
            self.current_log_file = os.path.join(self.log_dir, log_filename)
            self.current_python_path = current_python
            
            # 创建日志文件并写入头部信息
            with open(self.current_log_file, 'w', encoding='utf-8') as f:
                f.write(f"=== Nuitka打包工具日志 ===\n")
                f.write(f"开始时间: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"Python路径: {current_python}\n")
                f.write(f"日志文件: {self.current_log_file}\n")
                f.write(f"{'='*50}\n\n")
            
        except Exception as e:
            print(f"初始化日志失败: {str(e)}")
    
    def _write_to_log_file(self, message, tag=None):
        """写入日志到文件"""
        try:
            if self.current_log_file and os.path.exists(self.current_log_file):
                with open(self.current_log_file, 'a', encoding='utf-8') as f:
                    # 获取包含毫秒的时间戳
                    current_time = time.time()
                    timestamp_ms = time.strftime("%Y%m%d %H:%M:%S", time.localtime(current_time)) + f":{int((current_time % 1) * 1000):03d}"
                    tag_str = f"[{tag.upper()}] " if tag else ""
                    f.write(f"{timestamp_ms} {tag_str}{message}")
                    f.flush()  # 立即刷新到磁盘
        except Exception as e:
            print(f"写入日志文件失败: {str(e)}")
    
    def _check_python_environment_change(self):
        """检查Python环境是否发生变化，如果变化则记录到界面日志
        
        Returns:
            bool: 如果环境发生变化返回True，否则返回False
        """
        try:
            current_python = self.python_combo.currentText().strip() if hasattr(self, 'python_combo') else sys.executable
            
            # 如果current_python_path为None，说明是首次初始化，不认为是环境变化
            if self.current_python_path is None:
                # 首次初始化，直接设置当前路径，不触发环境变化检测
                self.current_python_path = current_python
                return False
            
            # 如果当前选择为空或与之前相同，不认为是环境变化
            if not current_python or current_python == self.current_python_path:
                return False
                
            # Python环境发生变化，只记录到界面日志，不创建新日志文件
            self.log_message(f"🔄 检测到Python环境变化: {self.current_python_path} -> {current_python}\n", "info")
            self.log_message(f"📝 注意：日志文件管理已改为手动导出模式\n", "info")
            self.current_python_path = current_python
            return True
        except Exception as e:
            print(f"检查Python环境变化失败: {str(e)}")
            return False
    
    def log_message(self, message, tag=None):
        """记录日志到界面"""
        # 获取包含毫秒的时间戳
        current_time = time.time()
        timestamp_ms = time.strftime("%Y%m%d %H:%M:%S", time.localtime(current_time)) + f":{int((current_time % 1) * 1000):03d}"
        
        # 添加到日志缓冲区
        if self.continuous_logging:
            log_entry = {
                'timestamp': timestamp_ms,
                'message': message,
                'tag': tag,
                'type': 'system'
            }
            self.log_buffer.append(log_entry)
            
            # 限制缓冲区大小
            if len(self.log_buffer) > self.max_log_buffer_size:
                self.log_buffer.pop(0)
        
        # 添加带颜色的文本到界面
        cursor = self.log_text.textCursor()
        cursor.movePosition(QTextCursor.End)
        
        # 日志行数控制 (最大500000行)
        MAX_LOG_LINES = 500000
        if self.log_text.document().blockCount() > MAX_LOG_LINES:
            cursor.setPosition(0)
            for _ in range(1000):  # 删除前1000行
                cursor.movePosition(QTextCursor.Down, QTextCursor.KeepAnchor)
            cursor.removeSelectedText()
            cursor.movePosition(QTextCursor.End)
        
        # 设置文本颜色
        if tag == "error":
            text_color = QColor("#FF6B6B")  # 红色
        elif tag == "success":
            text_color = QColor("#36C5F0")  # 蓝色
        elif tag == "warning":
            text_color = QColor("#FFBA49")  # 橙色
        elif tag == "info":
            text_color = QColor("#34A853")  # 绿色
        else:
            text_color = QColor("#4C5270")  # 深蓝色
        
        self.log_text.setTextColor(text_color)
        
        # 在消息前添加时间戳
        timestamp_message = f"[{timestamp_ms}] {message}"
        cursor.insertText(timestamp_message)
        cursor.movePosition(QTextCursor.End)
        
        # 只有在自动滚动状态下才滚动到底部
        if self.auto_scroll:
            self.log_text.setTextCursor(cursor)
            self.log_text.ensureCursorVisible()
    
    def log_user_action(self, action, details=""):
        """记录用户操作"""
        if not self.user_action_logging:
            return
            
        # 获取包含毫秒的时间戳
        current_time = time.time()
        timestamp_ms = time.strftime("%Y%m%d %H:%M:%S", time.localtime(current_time)) + f":{int((current_time % 1) * 1000):03d}"
        
        action_entry = {
            'timestamp': timestamp_ms,
            'action': action,
            'details': details
        }
        
        self.user_actions.append(action_entry)
        
        # 限制用户操作记录数量
        if len(self.user_actions) > self.max_user_actions:
            self.user_actions.pop(0)
        
        # 在日志中显示用户操作
        action_message = f"👤 用户操作: {action}"
        if details:
            action_message += f" - {details}"
        action_message += "\n"
        
        self.log_message(action_message, "info")
        
        # 同时添加到日志缓冲区
        if self.continuous_logging:
            log_entry = {
                'timestamp': timestamp_ms,
                'message': action_message,
                'tag': 'info',
                'type': 'user_action'
            }
            self.log_buffer.append(log_entry)
    
    def update_continuous_log(self):
        """更新连续日志显示"""
        if not self.continuous_logging or not self.log_buffer:
            return
            
        try:
            # 获取当前日志文本
            current_text = self.log_text.toPlainText()
            
            # 检查是否有新的日志需要添加
            if self.log_buffer:
                # 这里可以添加更复杂的连续日志处理逻辑
                # 例如：将缓冲区的日志写入文件，或者进行其他处理
                pass
                
        except Exception as e:
            print(f"更新连续日志失败: {str(e)}")
    
    def get_continuous_log_content(self):
        """获取连续日志内容"""
        if not self.log_buffer:
            return ""
            
        # 获取包含毫秒的时间戳
        current_time = time.time()
        timestamp_ms = time.strftime("%Y%m%d %H:%M:%S", time.localtime(current_time)) + f":{int((current_time % 1) * 1000):03d}"
        
        log_content = "# 连续日志记录\n"
        log_content += f"# 生成时间: {timestamp_ms}\n"
        log_content += f"# 总日志条数: {len(self.log_buffer)}\n\n"
        
        for entry in self.log_buffer:
            timestamp = entry['timestamp']
            message = entry['message'].rstrip()
            tag = entry.get('tag', '')
            log_type = entry.get('type', 'system')
            
            if log_type == 'user_action':
                log_content += f"{timestamp} [用户操作] {message}\n"
            else:
                tag_str = f"[{tag.upper()}] " if tag else ""
                log_content += f"{timestamp} {tag_str}{message}\n"
        
        return log_content
    
    def get_user_actions_summary(self):
        """获取用户操作摘要"""
        if not self.user_actions:
            return ""
            
        # 获取包含毫秒的时间戳
        current_time = time.time()
        timestamp_ms = time.strftime("%Y%m%d %H:%M:%S", time.localtime(current_time)) + f":{int((current_time % 1) * 1000):03d}"
        
        summary = "# 用户操作记录摘要\n"
        summary += f"# 记录时间: {timestamp_ms}\n"
        summary += f"# 总操作次数: {len(self.user_actions)}\n\n"
        
        for action in self.user_actions:
            timestamp = action['timestamp']
            action_name = action['action']
            details = action.get('details', '')
            
            summary += f"{timestamp} - {action_name}"
            if details:
                summary += f" : {details}"
            summary += "\n"
        
        return summary
    
    # ================= 插件加载 =================
    
    def load_plugins(self):
        """动态加载插件列表"""
        plugins_path = os.path.join(self.temp_dir, "plugins.json")
        try:
            # 检查插件配置是否存在
            if not os.path.exists(plugins_path):
                # 创建默认插件配置
                default_plugins = [
                    "tk-inter", "pyside6", "pyqt5", "PIL", "numpy", "pandas", 
                    "matplotlib", "pygame", "opencv-python", "pycryptodome",
                    "requests", "sqlalchemy", "django", "flask", "upx"
                ]
                with open(plugins_path, "w") as f:
                    json.dump({"plugins": default_plugins}, f)
                
                self.plugin_list.addItems(default_plugins)
            else:
                # 加载插件
                with open(plugins_path, "r") as f:
                    plugins_data = json.load(f)
                
                self.plugin_list.addItems(plugins_data["plugins"])
                
        except Exception as e:
            self.log_message(f"⚠ 加载插件失败: {str(e)}\n", "warning")
            # 添加默认插件作为后备
            default_fallback = ["tk-inter", "pyqt5", "upx", "requests"]
            self.plugin_list.addItems(default_fallback)
    
    # ================= 配置管理 =================
    
    def save_config(self):
        config = {
            "mode": self.mode_var,
            "optimize": self.opt_var,
            "jobs": self.jobs_var,
            "compiler": self.compiler_var,
            "use_lto": self.lto_var,
            "use_upx": self.upx_var,
            "upx_level": self.upx_level,
            "script": self.script_entry.text(),
            "output_dir": self.output_entry.text(),
            "exe_name": self.name_entry.text(),
            "icon": self.icon_entry.text(),
            "upx_path": self.upx_path_entry.text(),
            "cleanup_cache": self.cleanup_cache,
            "console": self.console_var,
            "python_path": self.python_combo.currentText(),

            "plugins": [item.text() for item in self.plugin_list.selectedItems()],
            "dependencies": [self.deps_list.item(i).text() for i in range(self.deps_list.count())]
        }
        
        try:
            with open(self.config_path, "w", encoding="utf-8") as f:
                json.dump(config, f, indent=2)
        except Exception as e:
            self.log_message(f"保存配置失败: {e}\n", "error")
    
    def load_config(self):
        try:
            if os.path.exists(self.config_path):
                with open(self.config_path, "r", encoding="utf-8") as f:
                    config = json.load(f)
                    
                self.mode_var = config.get("mode", "onefile")
                if hasattr(self, 'onefile_rb') and self.onefile_rb is not None:
                    if self.mode_var == "onefile":
                        self.onefile_rb.setChecked(True)
                    else:
                        if hasattr(self, 'standalone_rb') and self.standalone_rb is not None:
                            self.standalone_rb.setChecked(True)
                
                self.platform_var = "windows"  # 固定为Windows平台
                # 注意：windows_rb不存在，移除这行代码
                # 延迟调用update_platform，确保UI元素已初始化
                QTimer.singleShot(0, lambda: self.update_platform("windows"))
                
                self.opt_var = config.get("optimize", 1)
                if hasattr(self, 'opt_group') and self.opt_group is not None:
                    buttons = self.opt_group.buttons()
                    if len(buttons) >= 3:
                        if self.opt_var == 0:
                            buttons[0].setChecked(True)
                        elif self.opt_var == 1:
                            buttons[1].setChecked(True)
                        else:
                            buttons[2].setChecked(True)
                
                self.jobs_var = config.get("jobs", min(4, os.cpu_count()))
                if hasattr(self, 'jobs_slider') and self.jobs_slider is not None:
                    self.jobs_slider.setValue(self.jobs_var)
                
                self.compiler_var = config.get("compiler", "mingw")
                if hasattr(self, 'msvc_rb') and self.msvc_rb is not None and hasattr(self, 'mingw_rb') and self.mingw_rb is not None:
                    if self.compiler_var == "msvc":
                        self.msvc_rb.setChecked(True)
                    else:
                        self.mingw_rb.setChecked(True)
                
                self.lto_var = config.get("use_lto", "yes")
                if hasattr(self, 'lto_group') and self.lto_group is not None:
                    if self.lto_var == "off":
                        self.lto_group.button(0).setChecked(True)  # 第一个按钮是off
                    elif self.lto_var == "yes":
                        self.lto_group.button(1).setChecked(True)  # 第二个按钮是yes
                    elif self.lto_var == "full":
                        self.lto_group.button(2).setChecked(True)  # 第三个按钮是full
                
                self.upx_var = config.get("use_upx", False)
                if hasattr(self, 'upx_cb') and self.upx_cb is not None:
                    self.upx_cb.setChecked(self.upx_var)
                
                self.upx_level = config.get("upx_level", "best")
                if hasattr(self, 'upx_level_combo') and self.upx_level_combo is not None:
                    try:
                        self.upx_level_combo.setCurrentIndex(["best", "normal", "fast"].index(self.upx_level))
                    except (ValueError, IndexError):
                        pass  # 如果upx_level值无效，忽略错误
                
                self.console_var = config.get("console", "disable")
                if hasattr(self, 'console_enable_rb') and self.console_enable_rb is not None and hasattr(self, 'console_disable_rb') and self.console_disable_rb is not None:
                    if self.console_var == "enable":
                        self.console_enable_rb.setChecked(True)
                    else:
                        self.console_disable_rb.setChecked(True)
                
                self.cleanup_cache = config.get("cleanup_cache", True)
                if hasattr(self, 'cleanup_cb') and self.cleanup_cb is not None:
                    self.cleanup_cb.setChecked(self.cleanup_cache)
                
                # 安全设置文本框内容
                if hasattr(self, 'script_entry') and self.script_entry is not None:
                    self.script_entry.setText(config.get("script", ""))
                if hasattr(self, 'output_entry') and self.output_entry is not None:
                    self.output_entry.setText(config.get("output_dir", ""))
                if hasattr(self, 'name_entry') and self.name_entry is not None:
                    self.name_entry.setText(config.get("exe_name", ""))
                if hasattr(self, 'icon_entry') and self.icon_entry is not None:
                    self.icon_entry.setText(config.get("icon", ""))
                if hasattr(self, 'upx_path_entry') and self.upx_path_entry is not None:
                    self.upx_path_entry.setText(config.get("upx_path", ""))
                if hasattr(self, 'python_combo') and self.python_combo is not None:
                    self.python_combo.setCurrentText(config.get("python_path", ""))
                
                # 安全设置插件列表
                if hasattr(self, 'plugin_list') and self.plugin_list is not None:
                    plugins = config.get("plugins", [])
                    for i in range(self.plugin_list.count()):
                        item = self.plugin_list.item(i)
                        if item and item.text() in plugins:
                            item.setSelected(True)
                
                # 安全设置依赖列表
                if hasattr(self, 'deps_list') and self.deps_list is not None:
                    self.deps_list.clear()
                    for dep in config.get("dependencies", []):
                        self.deps_list.addItem(dep)
                
                self.update_jobs(self.jobs_var)
                
        except Exception as e:
            self.log_message(f"加载配置失败: {e}\n", "error")
    
    def closeEvent(self, event):
        """处理窗口关闭事件"""
        # 输出性能统计信息
        self._print_performance_stats()
        
        # 调用父类的关闭事件处理方法
        super().closeEvent(event)

        event.accept()
    
    def _print_performance_stats(self):
        """打印性能统计信息"""
        if hasattr(self, 'detection_stats') and self.detection_stats:
            self.log_message("\n=== 虚拟环境检测性能统计 ===\n", "info")
            for detection_type, stats in self.detection_stats.items():
                avg_time = stats['total_time'] / stats['count'] if stats['count'] > 0 else 0
                self.log_message(f"{detection_type}:\n", "info")
                self.log_message(f"  检测次数: {stats['count']}\n", "info")
                self.log_message(f"  总耗时: {stats['total_time']:.2f}秒\n", "info")
                self.log_message(f"  平均耗时: {avg_time:.2f}秒\n", "info")
                self.log_message(f"  找到的环境数: {stats.get('found_count', 0)}\n", "info")
            self.log_message("========================\n", "info")
    
    def uses_tkinter(self, script_path):
        """检查脚本是否使用了tkinter模块"""
        if not os.path.exists(script_path):
            return False
        
        try:
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查常见的tkinter导入模式
            tkinter_patterns = [
                r'^\s*import\s+tkinter(?:\s|$)',
                r'^\s*from\s+tkinter(?:\s+import\s+\w+(?:,\s*\w+)*)?',  # from tkinter import ttk, filedialog
                r'^\s*import\s+Tkinter(?:\s|$)',
                r'^\s*from\s+Tkinter(?:\s+import\s+\w+(?:,\s*\w+)*)?',  # from Tkinter import ttk, filedialog
                r'^\s*import\s+\w+\s+as\s+tk\b',  # import tkinter as tk
            ]
            
            # 将内容按行分割，逐行检查
            lines = content.split('\n')
            for line in lines:
                # 跳过注释行
                if line.strip().startswith('#'):
                    continue
                for pattern in tkinter_patterns:
                    if re.search(pattern, line):
                        return True
            
            return False
        except Exception as e:
            self.log_message(f"⚠ 检查tkinter使用情况时出错: {str(e)}\n", "warning")
            return False
    
    def uses_pyside6(self, script_path):
        """检查脚本是否使用了PySide6模块"""
        if not os.path.exists(script_path):
            return False
        
        try:
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查常见的PySide6导入模式
            pyside6_patterns = [
                r'import\s+PySide6',
                r'from\s+PySide6',
                r'import\s+PyQt6',
                r'from\s+PyQt6',
                r'import\s+Shiboken',
                r'from\s+Shiboken'
            ]
            
            for pattern in pyside6_patterns:
                if re.search(pattern, content):
                    return True
            
            return False
        except Exception as e:
            self.log_message(f"⚠ 检查PySide6使用情况时出错: {str(e)}\n", "warning")
            return False
    
    def uses_pyqt5(self, script_path):
        """检查脚本是否使用了PyQt5模块"""
        if not os.path.exists(script_path):
            return False
        
        try:
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查常见的PyQt5导入模式
            pyqt5_patterns = [
                r'import\s+PyQt5',
                r'from\s+PyQt5',
                r'import\s+sip',
                r'from\s+sip'
            ]
            
            for pattern in pyqt5_patterns:
                if re.search(pattern, content):
                    return True
            
            return False
        except Exception as e:
            self.log_message(f"⚠ 检查PyQt5使用情况时出错: {str(e)}\n", "warning")
            return False
    
    def uses_pil(self, script_path):
        """检查脚本是否使用了PIL/Pillow模块"""
        if not os.path.exists(script_path):
            return False
        
        try:
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查常见的PIL导入模式
            pil_patterns = [
                r'import\s+PIL',
                r'from\s+PIL',
                r'import\s+Image',
                r'from\s+Image',
                r'import\s+Pillow',
                r'from\s+Pillow'
            ]
            
            for pattern in pil_patterns:
                if re.search(pattern, content):
                    return True
            
            return False
        except Exception as e:
            self.log_message(f"⚠ 检查PIL使用情况时出错: {str(e)}\n", "warning")
            return False
    
    def uses_numpy(self, script_path):
        """检查脚本是否使用了numpy模块"""
        if not os.path.exists(script_path):
            return False
        
        try:
            with open(script_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查常见的numpy导入模式
            numpy_patterns = [
                r'import\s+numpy',
                r'from\s+numpy',
                r'import\s+np\s*$',
                r'from\s+np'
            ]
            
            for pattern in numpy_patterns:
                if re.search(pattern, content):
                    return True
            
            return False
        except Exception as e:
            self.log_message(f"⚠ 检查numpy使用情况时出错: {str(e)}\n", "warning")
            return False
    
    def on_script_path_changed(self):
        """脚本路径变化时的处理函数
        
        当脚本路径输入框的内容发生变化时，自动同步更新运行Python文件输入框的内容。
        确保运行Python文件输入框始终显示与脚本路径相同的文件路径。
        """
        # 获取脚本路径输入框的当前内容
        script_path = self.script_entry.text().strip()
        
        # 同步更新运行Python文件输入框的内容
        self.run_py_entry.setText(script_path)
        
        # 记录同步信息（可选，用于调试）
        if script_path:
            self.log_message(f"🔄 已同步运行Python文件路径: {script_path}\n", "info")
    
    def run_python_file(self):
        """运行脚本路径中的Python文件"""
        # 获取脚本路径中的Python文件
        file_path = self.script_entry.text().strip()
        if not file_path:
            self.log_message("⚠ 请先在脚本路径中选择要运行的Python文件\n", "warning")
            return
        
        if not os.path.exists(file_path):
            self.log_message(f"⚠ 脚本文件不存在: {file_path}\n", "error")
            return
        
        # 检查是否为Python文件
        if not file_path.lower().endswith('.py'):
            self.log_message(f"⚠ 文件不是Python文件: {file_path}\n", "error")
            return
        
        # 获取用户选择的Python解释器路径
        python_cmd = self.python_combo.currentText().strip() if self.python_combo.currentText().strip() else sys.executable
        
        self.log_message(f"🚀 开始运行Python文件: {file_path}\n", "info")
        self.log_message(f"🔧 使用Python解释器: {python_cmd}\n", "info")
        
        # 检查是否为conda环境
        conda_env_name = self._get_conda_env_name(python_cmd)
        
        try:
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            if conda_env_name:
                # 如果是conda环境，先激活环境再运行
                activate_cmd = f'conda activate {conda_env_name} && '
                full_cmd = activate_cmd + f'python "{file_path}"'
                self.log_message(f"📋 执行命令: {full_cmd}\n", "info")
                
                # 使用subprocess执行命令
                proc = subprocess.Popen(
                    full_cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    startupinfo=startupinfo,
                    shell=True
                )
            else:
                # 直接运行Python文件
                cmd = [python_cmd, file_path]
                self.log_message(f"📋 执行命令: {' '.join(cmd)}\n", "info")
                
                # 使用subprocess执行命令
                proc = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    startupinfo=startupinfo,
                    shell=False
                )
            
            # 读取并输出运行结果
            for line in proc.stdout:
                self.log_message(f"📤 {line.strip()}\n", "output")
            
            # 等待进程结束
            return_code = proc.wait()
            
            if return_code == 0:
                self.log_message("✅ Python文件运行完成\n", "success")
            else:
                self.log_message(f"⚠ Python文件运行结束，返回码: {return_code}\n", "warning")
                
        except Exception as e:
            self.log_message(f"❌ 运行Python文件时出错: {str(e)}\n", "error")
    
    def run_pkg_management(self):
        """执行包管理命令（安装/卸载）"""
        package_name = self.pkg_cmd_entry.text().strip()
        if not package_name:
            self.log_message("⚠ 请输入包名\n", "warning")
            return
        
        # 获取选择的包管理器和操作类型
        pkg_manager = self.pkg_manager_combo.currentText()
        action = self.pkg_action_combo.currentText()
        
        # 获取用户选择的Python解释器路径
        python_cmd = self.python_combo.currentText().strip() if self.python_combo.currentText().strip() else sys.executable
        
        action_text = "安装" if action == "install" else "卸载"
        self.log_message(f"📦 开始{action_text}包: {package_name}\n", "info")
        self.log_message(f"🔧 使用包管理器: {pkg_manager}\n", "info")
        self.log_message(f"🐍 使用Python解释器: {python_cmd}\n", "info")
        
        # 检查是否为conda环境
        conda_env_name = self._get_conda_env_name(python_cmd)
        
        try:
            startupinfo = None
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = 0
            
            if conda_env_name:
                # 如果是conda环境，先激活环境再执行命令
                activate_cmd = f'conda activate {conda_env_name} && '
                
                if pkg_manager == "conda":
                    if action == "install":
                        full_cmd = activate_cmd + f'conda install {package_name} -y'
                    else:  # uninstall
                        full_cmd = activate_cmd + f'conda remove {package_name} -y'
                elif pkg_manager == "mamba":
                    if action == "install":
                        full_cmd = activate_cmd + f'mamba install {package_name} -y'
                    else:  # uninstall
                        full_cmd = activate_cmd + f'mamba remove {package_name} -y'
                else:  # pip
                    if action == "install":
                        full_cmd = activate_cmd + f'pip install {package_name}'
                    else:  # uninstall
                        full_cmd = activate_cmd + f'pip uninstall {package_name} -y'
                
                self.log_message(f"📋 执行命令: {full_cmd}\n", "info")
                
                # 使用subprocess执行命令
                proc = subprocess.Popen(
                    full_cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    startupinfo=startupinfo,
                    shell=True
                )
            else:
                # 直接执行包管理命令
                if pkg_manager == "conda":
                    if action == "install":
                        cmd = ["conda", "install", package_name, "-y"]
                    else:  # uninstall
                        cmd = ["conda", "remove", package_name, "-y"]
                elif pkg_manager == "mamba":
                    if action == "install":
                        cmd = ["mamba", "install", package_name, "-y"]
                    else:  # uninstall
                        cmd = ["mamba", "remove", package_name, "-y"]
                else:  # pip
                    if action == "install":
                        cmd = [python_cmd, "-m", "pip", "install", package_name]
                    else:  # uninstall
                        cmd = [python_cmd, "-m", "pip", "uninstall", package_name, "-y"]
                
                self.log_message(f"📋 执行命令: {' '.join(cmd)}\n", "info")
                
                # 使用subprocess执行命令
                proc = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    bufsize=1,
                    universal_newlines=True,
                    startupinfo=startupinfo,
                    shell=False
                )
            
            # 读取并输出执行结果
            for line in proc.stdout:
                self.log_message(f"📦 {line.strip()}\n", "output")
            
            # 等待进程结束
            return_code = proc.wait()
            
            if return_code == 0:
                self.log_message(f"✅ 包 {package_name} {action_text}完成\n", "success")
            else:
                self.log_message(f"⚠ 包{action_text}结束，返回码: {return_code}\n", "warning")
                
        except Exception as e:
            self.log_message(f"❌ {action_text}包时出错: {str(e)}\n", "error")
    
    def on_python_combo_changed(self, text):
        """当Python解释器选择改变时，输出Nuitka和Python版本信息"""
        if text.strip():  # 只有当选择的文本非空时才输出版本信息
            # 检查Python环境变化
            env_changed = self._check_python_environment_change()
            
            # 添加分隔线，区分启动日志和环境信息
            self.log_message("\n" + "="*50 + "\n", "info")
            
            # 只有在环境确实变化时才显示环境变更日志
            if env_changed:
                self.log_message("🔄 Python环境变更，重新检测版本信息...\n", "info")
            else:
                self.log_message("🔍 检测Python和Nuitka版本信息...\n", "info")
                
            self.log_message("="*50 + "\n", "info")
            
            # 获取Python版本
            python_version = self._get_python_version(text)
            if python_version:
                self.log_message(f"🐍 Python版本: {python_version}\n", "info")
            else:
                self.log_message(f"🐍 Python版本: 未知\n", "warning")
            
            # 获取Nuitka版本
            nuitka_version = self._get_nuitka_version(text)
            if nuitka_version:
                self.log_message(f"📦 Nuitka版本: {nuitka_version}\n", "info")
            else:
                # 处理检测失败的情况
                self.log_message(f"📦 Nuitka版本: 未安装\n", "warning")
                self.log_message("请使用以下命令安装Nuitka：\n", "info")
                self.log_message("# 使用pip安装 (推荐)\n", "info")
                self.log_message("nuitka稳定版 pip install nuitka\n", "info")
                self.log_message("nuitka测试版 pip install -U https://github.com/Nuitka/Nuitka/archive/develop.zip \n", "info")
                self.log_message("# 使用conda安装\n", "info")
                self.log_message("conda install -c conda-forge nuitka\n", "info")
                self.log_message("# 使用mamba安装 (更快)\n", "info")
                self.log_message("mamba install -c conda-forge nuitka\n", "info")
                self.log_message("# 升级到最新版本\n", "info")
                self.log_message("pip install --upgrade nuitka\n", "info")
    
    def closeEvent(self, event):
        """窗口关闭事件处理 - 清理所有线程资源"""
        try:
            # 停止定时器
            if hasattr(self, 'timer') and self.timer.isActive():
                self.timer.stop()
            
            # 取消所有线程
            if hasattr(self, 'thread_manager'):
                self.log_message("🧹 正在清理后台线程...\n", "info")
                self.thread_manager.cancel_all_threads()
                
                # 等待线程清理完成
                import time
                timeout = 3  # 3秒超时
                start_time = time.time()
                
                while self.thread_manager.get_active_thread_count() > 0:
                    if time.time() - start_time > timeout:
                        self.log_message("⚠ 部分线程未能在超时时间内完成，强制关闭\n", "warning")
                        break
                    QApplication.processEvents()  # 保持UI响应
                    time.sleep(0.1)
                
                self.log_message("✅ 线程清理完成\n", "success")
            
            # 保存配置
            if hasattr(self, 'config_path'):
                self.save_config()
                
        except Exception as e:
            print(f"窗口关闭时清理资源出错: {str(e)}")
        
        # 调用父类的关闭事件
        super().closeEvent(event)


if __name__ == "__main__":
    import argparse
    
    # 创建命令行参数解析器
    parser = argparse.ArgumentParser(description="Nuitka EXE 打包工具")
    parser.add_argument("--script", help="要打包的Python脚本路径", required=False)
    parser.add_argument("--output-dir", help="输出目录", required=False)
    parser.add_argument("--onefile", help="是否打包为单个exe文件", action="store_true")
    parser.add_argument("--name", help="生成的exe文件名", required=False)
    parser.add_argument("--console", help="是否启用控制台", choices=["enable", "disable"], default="disable")
    parser.add_argument("--icon", help="图标文件路径", required=False)
    
    # 解析命令行参数
    args = parser.parse_args()
    
    # 如果提供了脚本参数，则执行打包操作
    if args.script:
        # 创建应用实例
        app = QApplication.instance()
        if app is None:
            app = QApplication(sys.argv)
        
        # 创建打包器实例
        packager = NuitkaPackager()
        
        # 设置参数
        if hasattr(packager, 'script_entry'):
            packager.script_entry.setText(args.script)
        if args.output_dir and hasattr(packager, 'output_entry'):
            packager.output_entry.setText(args.output_dir)
        if args.name and hasattr(packager, 'name_entry'):
            packager.name_entry.setText(args.name)
        if args.icon and hasattr(packager, 'icon_entry'):
            packager.icon_entry.setText(args.icon)
        
        # 设置控制台选项
        if hasattr(packager, 'console_enable_rb') and hasattr(packager, 'console_disable_rb'):
            if args.console == "enable":
                packager.console_enable_rb.setChecked(True)
            else:
                packager.console_disable_rb.setChecked(True)
        
        # 设置打包模式
        if hasattr(packager, 'onefile_rb') and hasattr(packager, 'standalone_rb'):
            if args.onefile:
                packager.onefile_rb.setChecked(True)
            else:
                packager.standalone_rb.setChecked(True)
        
        # 执行打包
        packager.start_packaging()
        
        # 退出应用
        sys.exit(0)
    else:
        # 没有提供脚本参数，启动GUI界面
        app = QApplication(sys.argv)
        # 可选：为整个应用设置图标（影响所有窗口）
        # app.setWindowIcon(QIcon("F:\Python\ico-files\Pythontoexeico.ico"))
        # 可选：为应用设置名称（影响任务栏和窗口标题）
        # app.setApplicationName("Nuitka打包工具")
        packager = NuitkaPackager()
        packager.show()
        sys.exit(app.exec())