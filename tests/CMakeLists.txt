add_executable(
    gold-test
    ${CMAKE_CURRENT_SOURCE_DIR}/test.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/parsing.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/serialization.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/bindings.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/evaluate.cpp
    )
