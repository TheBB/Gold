import goldpy


def test_ints():
    assert goldpy.evaluate_string('1') == 1


def test_callables():
    f = goldpy.evaluate_string('(x,y) => x + y')
    assert f(1, 2) == 3

    g = goldpy.evaluate_string('{x, y} => x + y')
    assert g(x=1, y=2) == 3
    assert g(x=1, y=2, z=None) == 3

    h = goldpy.evaluate_string('(f, x, y) => f(x, y)')
    assert h((lambda x, y: x + y), 1, 2) == 3

    h = goldpy.evaluate_string('(f, x, y=4) => f(x, y)')
    assert h((lambda x, y: x + y), 1) == 5
    assert h((lambda x, y: x + y), 1, 10) == 11

    h = goldpy.evaluate_string('(f, x, y=4) => f(x: x, y: y)')
    assert h((lambda x, y: x + y), 1) == 5
    assert h((lambda x, y: x + y), 1, 10) == 11
