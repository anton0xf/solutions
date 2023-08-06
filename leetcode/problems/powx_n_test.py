import problems.powx_n as sol
from pytest import approx

s = sol.Solution()


def test():
    assert s.myPow(2., 10) == approx(1024.)
    assert s.myPow(2.1, 3) == approx(9.261)
    assert s.myPow(2., -2) == approx(0.25)
