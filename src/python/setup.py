import os
import platform
import sys
import subprocess


from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext

__version__ = "0.1.0"


class CMakeExtension(Extension):
    def __init__(self, name, cmake_lists_dir='.', sources=[], **kwa):
        Extension.__init__(self, name, sources=sources, **kwa)
        self.cmake_lists_dir = os.path.abspath(cmake_lists_dir)


class CMakeBuild(build_ext):

    def build_extensions(self):
        for ext in self.extensions:
            extdir = os.path.abspath(os.path.dirname(self.get_ext_fullpath(ext.name)))
            cmake_args = [
                '-DCMAKE_BUILD_TYPE=Release',
                f'-B{os.path.abspath(self.build_temp)}',
                f'-S{ext.cmake_lists_dir}',
                f'-DCMAKE_LIBRARY_OUTPUT_DIRECTORY_RELEASE={extdir}',
                f'-DCMAKE_ARCHIVE_OUTPUT_DIRECTORY_RELEASE={self.build_temp}',
            ]

            if platform.system() == 'Windows':
                plat = ('x64' if platform.architecture()[0] == '64bit' else 'Win32')
                cmake_args += [
                    '-DCMAKE_WINDOWS_EXPORT_ALL_SYMBOLS=TRUE',
                    f'-DCMAKE_RUNTIME_OUTPUT_DIRECTORY_RELEASE={extdir}',
                ]
                if self.compiler.compiler_type == 'msvc':
                    cmake_args += [
                        f'-DCMAKE_GENERATOR_PLATFORM={plat}',
                    ]
                else:
                    cmake_args += [
                        '-G', 'MinGW Makefiles',
                    ]

            if not os.path.exists(self.build_temp):
                os.makedirs(self.build_temp)

            # Config and build the extension
            subprocess.check_call(['cmake', ext.cmake_lists_dir] + cmake_args, cwd=self.build_temp)
            subprocess.check_call(['cmake', '--build', '.', '--config', 'Release'], cwd=self.build_temp)


setup(
    name="pygold",
    version=__version__,
    author="Eivind Fonn",
    author_email="evfonn@gmail.com",
    url="https://github.com/TheBB/Gold",
    description="Python bindings to the Gold language",
    long_description="",
    ext_modules=[CMakeExtension('pygold', '../../')],
    cmdclass={"build_ext": CMakeBuild},
    zip_safe=False,
    python_requires=">=3.6",
)
