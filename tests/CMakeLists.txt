function(add_unit_test _target)
    find_package(GTest REQUIRED)
    add_executable(${_target})
    target_link_libraries(${_target} PRIVATE GTest::gtest GTest::gtest_main)
    add_test(NAME ${_target} COMMAND ${_target})
    target_include_directories(${_target} PRIVATE ${LLVM_SUPPORT_SOURCE_DIR}/util/include)
endfunction()

add_subdirectory(ADT)

add_subdirectory(Support)