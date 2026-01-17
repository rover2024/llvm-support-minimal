if(LLVM_SUPPORT_DISABLE_EXCEPTIONS)
    if(MSVC)
        set(CMAKE_C_FLAGS "${CMAKE_CXX_FLAGS} /EHsc-")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /EHsc-")
    else()
        set(CMAKE_C_FLAGS "${CMAKE_CXX_FLAGS} -fno-exceptions")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-exceptions")
    endif()
endif()

if(LLVM_SUPPORT_DISABLE_RTTI)
    if(MSVC)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /GR-")
    else()
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
    endif()
endif()

if(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-z,defs")
endif()

add_subdirectory(Support)

if(LLVM_SUPPORT_INSTALL)
    # Add install target
    set(_install_dir ${CMAKE_INSTALL_LIBDIR}/cmake/${LLVM_SUPPORT_INSTALL_NAME})

    # Add version file
    write_basic_package_version_file(
        "${CMAKE_CURRENT_BINARY_DIR}/${LLVM_SUPPORT_INSTALL_NAME}ConfigVersion.cmake"
        VERSION ${PROJECT_VERSION}
        COMPATIBILITY AnyNewerVersion
    )

    # Add configuration file
    configure_package_config_file(
        ${CMAKE_CURRENT_LIST_DIR}/${LLVM_SUPPORT_INSTALL_NAME}Config.cmake.in
        "${CMAKE_CURRENT_BINARY_DIR}/${LLVM_SUPPORT_INSTALL_NAME}Config.cmake"
        INSTALL_DESTINATION ${_install_dir}
        NO_CHECK_REQUIRED_COMPONENTS_MACRO
    )

    # Install cmake files
    install(FILES
        "${CMAKE_CURRENT_BINARY_DIR}/${LLVM_SUPPORT_INSTALL_NAME}Config.cmake"
        "${CMAKE_CURRENT_BINARY_DIR}/${LLVM_SUPPORT_INSTALL_NAME}ConfigVersion.cmake"
        DESTINATION ${_install_dir}
    )

    # Install cmake targets files
    install(EXPORT ${LLVM_SUPPORT_INSTALL_NAME}Targets
        FILE "${LLVM_SUPPORT_INSTALL_NAME}Targets.cmake"
        NAMESPACE llvm-support::
        DESTINATION ${_install_dir}
    )

    install(DIRECTORY ${LLVM_SUPPORT_SOURCE_DIR}/include/
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
        FILES_MATCHING PATTERN "*.h"
    )
endif()