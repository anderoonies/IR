cmake_minimum_required(VERSION 3.7)
project(src)

set(CMAKE_CXX_STANDARD 11)

set(SOURCE_FILES
    compiler.cpp
    compiler.h
    IR.h
    main.cpp
    parser.cpp
    parser.h)

add_executable(src ${SOURCE_FILES})