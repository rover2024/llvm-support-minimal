file(GLOB _test_files "*.cpp")

foreach(_file IN LISTS _test_files)
    get_filename_component(_test_name ${_file} NAME_WE)
    add_unit_test(${_test_name})
    target_sources(${_test_name} PRIVATE ${_file})
    target_link_libraries(${_test_name} PRIVATE llvm-support)
endforeach()
