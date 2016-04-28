# find lit. Assume we are using external lit installed from pip
find_program(LIT_COMMAND lit)

# add the test suite
add_lit_testsuite(test-abc "Running the regression tests for Array Bounds Checks"
  ${CMAKE_CURRENT_SOURCE_DIR}
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS seahorn
  )
