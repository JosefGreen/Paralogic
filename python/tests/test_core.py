import numpy as np
from python.paralogic_core import huber_tension, jump_operator

def gradV(x):
    return 2 * x

def c1(x):
    return np.abs(x) - 1

def test_huber_quadratic():
    c = np.array([0.2, -0.2])
    expected = 0.5 * (c**2) / 0.5
    assert np.allclose(huber_tension(c, 0.5), expected)

def test_jump_satisfies_constraint():
    x0 = np.array([2.0])
    y = jump_operator(x0, gradV, [c1])
    assert np.all(c1(y) <= 0)
