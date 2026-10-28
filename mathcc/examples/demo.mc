# Guarded simplification demo
assume y > 0

a = (x*x)/x              # needs x != 0 -> runtime guard
b = sqrt(x^2)            # = abs(x), no guard needed
c = sin(y)^2 + cos(y)^2 + y/y    # y>0 proven -> no runtime guard
g = sqrt(z)*sqrt(z)      # needs z >= 0
h = ln(exp(x)) + exp(ln(y))
k = (w+1)/(w+1)          # guard on a compound subexpression
f = d(x^3*sin(x), x)     # symbolic derivative, then simplified
