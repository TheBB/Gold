add_executable(
    gold-test
    ${CMAKE_CURRENT_SOURCE_DIR}/test.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/object.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/parsing.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/serialization.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/bindings.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/evaluate.cpp
)

target_link_libraries(gold-test PRIVATE gold-nostdlib gold-stdlib)
target_include_directories(gold-test PRIVATE ${CMAKE_SOURCE_DIR}/src/lib/include)

if(GOLD_COVERAGE)
    setup_target_for_coverage_lcov(
        NAME gold-test-coverage
        EXECUTABLE $<TARGET_FILE:gold-test>
        DEPENDENCIES gold-test
        EXCLUDE
        "*/nlohmann/*" "*/vcpkg_installed/*" "*/pegtl/*" "/usr/*"
        "*tests*" "*src/bin*"
    )
endif()

add_test(NAME parsing COMMAND $<TARGET_FILE:gold-test> [parsing])
add_test(NAME serialization COMMAND $<TARGET_FILE:gold-test> [serialization])
add_test(NAME bindings COMMAND $<TARGET_FILE:gold-test> [bindings])
add_test(NAME evaluate COMMAND $<TARGET_FILE:gold-test> [evaluate])
