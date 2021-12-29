add_executable(
    gold-serialize
    ${CMAKE_CURRENT_SOURCE_DIR}/serializer.cpp
)

target_link_libraries(gold-serialize gold-nostdlib)


if(GOLD_BUILD_UTILS)

    add_executable(
        gold-to-json
        ${CMAKE_CURRENT_SOURCE_DIR}/main.cpp
    )

    target_link_libraries(gold-to-json gold-nostdlib gold-stdlib nlohmann_json cxxopts::cxxopts)

endif()
