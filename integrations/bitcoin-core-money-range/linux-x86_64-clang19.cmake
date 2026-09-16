# Header-only Linux cross configuration for generating Bitcoin Core's real
# compilation database on an Apple Silicon host. This does not link binaries.
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR x86_64)
set(CMAKE_SYSROOT "${CMAKE_CURRENT_LIST_DIR}/inputs/sysroot")
set(CMAKE_C_COMPILER "/opt/homebrew/opt/llvm@19/bin/clang")
set(CMAKE_CXX_COMPILER "/opt/homebrew/opt/llvm@19/bin/clang++")
set(CMAKE_C_COMPILER_TARGET x86_64-unknown-linux-gnu)
set(CMAKE_CXX_COMPILER_TARGET x86_64-unknown-linux-gnu)
set(CMAKE_C_FLAGS_INIT "-isystem ${CMAKE_SYSROOT}/usr/include/x86_64-linux-gnu")
set(CMAKE_CXX_FLAGS_INIT
    "-resource-dir=/opt/homebrew/opt/llvm@19/lib/clang/19 -nostdinc++ -isystem ${CMAKE_SYSROOT}/usr/include/c++/12 -isystem ${CMAKE_SYSROOT}/usr/include/x86_64-linux-gnu/c++/12 -isystem ${CMAKE_SYSROOT}/usr/include/x86_64-linux-gnu")
set(CMAKE_AR "/opt/homebrew/opt/llvm@19/bin/llvm-ar")
set(CMAKE_RANLIB "/opt/homebrew/opt/llvm@19/bin/llvm-ranlib")
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_PACKAGE ONLY)
