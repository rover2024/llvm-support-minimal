cmake_minimum_required(VERSION 3.16)

project(llvm-support VERSION 21.1.8 LANGUAGES CXX)

# ----------------------------------
# Build Options
# ----------------------------------
option(LLVM_SUPPORT_BUILD_SHARED "Build shared library" ON)
option(LLVM_SUPPORT_DISABLE_EXCEPTIONS "Disable C/C++ exceptions" ON)
option(LLVM_SUPPORT_DISABLE_RTTI "Disable C++ RTTI" ON)
option(LLVM_SUPPORT_BUILD_TESTS "Build test suite" OFF)
option(LLVM_SUPPORT_INSTALL "Install library" ON)

# ----------------------------------
# CMake Settings
# ----------------------------------
if(NOT DEFINED CMAKE_RUNTIME_OUTPUT_DIRECTORY)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/bin)
endif()

if(NOT DEFINED CMAKE_LIBRARY_OUTPUT_DIRECTORY)
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
endif()

if(NOT DEFINED CMAKE_ARCHIVE_OUTPUT_DIRECTORY)
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
endif()

if(MSVC)
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /manifest:no")
    set(CMAKE_MODULE_LINKER_FLAGS "${CMAKE_MODULE_LINKER_FLAGS} /manifest:no")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /manifest:no")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} /utf-8")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /utf-8")

    # if(NOT DEFINED CMAKE_DEBUG_POSTFIX)
    #     set(CMAKE_DEBUG_POSTFIX "d")
    # endif()
elseif(MINGW)
    set(CMAKE_STATIC_LIBRARY_PREFIX "")
    set(CMAKE_SHARED_LIBRARY_PREFIX "")
    set(CMAKE_IMPORT_LIBRARY_PREFIX "")
endif()

if(LLVM_SUPPORT_INSTALL)
    include(GNUInstallDirs)
    include(CMakePackageConfigHelpers)
endif()

# ----------------------------------
# Project Variables
# ----------------------------------
set(LLVM_SUPPORT_VERSION ${PROJECT_VERSION})
set(LLVM_SUPPORT_INSTALL_NAME ${PROJECT_NAME})
set(LLVM_SUPPORT_SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR})

# ----------------------------------
# Main Project
# ----------------------------------
add_subdirectory(lib)

if (LLVM_SUPPORT_BUILD_TESTS)
    add_subdirectory(tests)
endif()