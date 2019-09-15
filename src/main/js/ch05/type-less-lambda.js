const Lambda = {
  tru: (x) => (y) => x,
  fls: (x) => (y) => y,
  test: (b) => (m) => (n) => b(m)(n)(),
  c0: (s) => (z) => z,
  c1: (s) => (z) => s(z),
  c2: (s) => (z) => s(s(z)),
  c3: (s) => (z) => s(s(s(z))),
  realnat: (x) => x((acc) => acc + 1)(0),
  succ: (n) => (s) => (z) => s(n(s)(z)),
  plus: (n) => (m) => (s) => (z) => n(s)(m(s)(z)),
  times: (n) => (m) => n(Lambda.plus(m))(Lambda.c0),
  pred: (n) => (s) => (z) => n((x) => (y) => y(x(s)))((x) => z)((x) => x),
  z: (f) => ((x) => f((y) => x(x)(y)))((x) => f((y) => x(x)(y))),
  iszero: (x) => x((y) => Lambda.fls)(Lambda.tru)
}

const fct = Lambda.z((f) => (x) => Lambda.test(Lambda.iszero(Lambda.pred(x)))(() => Lambda.c1)(() => Lambda.times(x)(f(Lambda.pred(x)))))
const fib = Lambda.z((f) => (x) => Lambda.test(Lambda.iszero(Lambda.pred(x)))(() => x)(() => Lambda.plus(f(Lambda.pred(x)))(f(Lambda.pred(Lambda.pred(x))))))

