import goldpy


def test_ints():
    assert goldpy.eval_raw('1') == 1


def test_callables():
    f = goldpy.eval_raw('|x,y| x + y')
    assert f(1, 2) == 3

    g = goldpy.eval_raw('{|x, y|} x + y')
    assert g(x=1, y=2) == 3
    assert g(x=1, y=2, z=None) == 3

    h = goldpy.eval_raw('|f, x, y| f(x, y)')
    assert h((lambda x, y: x + y), 1, 2) == 3

    h = goldpy.eval_raw('|f, x, y=4| f(x, y)')
    assert h((lambda x, y: x + y), 1) == 5
    assert h((lambda x, y: x + y), 1, 10) == 11

    h = goldpy.eval_raw('|f, x, y=4| f(x: x, y: y)')
    assert h((lambda x, y: x + y), 1) == 5
    assert h((lambda x, y: x + y), 1, 10) == 11


def test_importer():
    def importer(path):
        return {
            'msg': f'you imported {path}',
        }

    assert goldpy.eval('import "test" as {msg}\nmsg', None, importer) == 'you imported test'
    assert goldpy.eval('import "manifold" as {msg}\nmsg', None, importer) == 'you imported manifold'
    assert goldpy.eval('import "std" as {info}\ninfo.distribution', None, importer) == 'gold'
