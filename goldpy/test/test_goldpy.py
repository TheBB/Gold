import goldpy


def test_ints():
    assert goldpy.evaluate_string('1') == 1
