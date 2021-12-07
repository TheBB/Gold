add_library(
    gold
    ${CMAKE_CURRENT_SOURCE_DIR}/gold.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/parsing.cpp
)

target_include_directories(gold PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)

find_package(fmt)
target_link_libraries(gold fmt::fmt taocpp::pegtl)
