import numpy as np

def huber_tension(c, delta):
    abs_c = np.abs(c)
    return np.where(
        abs_c <= delta,
        0.5 * (c**2) / delta,
        abs_c - 0.5 * delta
    )

def jump_operator(x, gradV, constraints, step=0.1, max_iter=100):
    y = x.copy()
    for _ in range(max_iter):
        y = y - step * gradV(y)
        if all(c(y) <= 0 for c in constraints):
            return y
    return y
