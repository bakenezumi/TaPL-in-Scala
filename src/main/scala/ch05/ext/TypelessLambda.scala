package ch05.ext

sealed trait Term
final case class TmVar(value: Any) extends Term {
  override def toString: String = s"$value"
}
final case class TmAbs(x: Term, t: Term) extends Term {
  override def toString: String = s"λ($x.$t)"
}
final case class TmApply(t1: Term, t2: Term) extends Term {
  override def toString: String = s"($t1 $t2)"
}

object TypelessLambda {
  def lambda(xs: Term*) =
    xs.init.init.foldRight(TmAbs(xs.init.last, xs.last))(TmAbs(_, _))
  def apply(xs: Term*) =
    xs.tail.tail.foldLeft(TmApply(xs.head, xs.tail.head))(TmApply(_, _))

  implicit class RichTerm(self: Term) {
    def apply(that: => Term): Term = {
      TmApply(self, that)
    }
    def eval(): Term = {
      TypelessLambda.eval(self)
    }
  }

  // substitution [x |-> s]t defined in TaPL p. 54
  def substitution(x: Term, t: Term, s: Term): Term = {
    println(s"  [$x |-> $s]$t")
    val ret = t match {
      case y if x == y            => s
      case TmAbs(y, t1) if x != y => TmAbs(y, substitution(x, t1, s))
      case TmApply(t1, t2) =>
        TmApply(substitution(x, t1, s), substitution(x, t2, s))
      case TmVar(y: String) if x.isInstanceOf[TmVar] && s.isInstanceOf[TmVar] =>
        TmVar(
          y.replaceAll(x.asInstanceOf[TmVar].value.toString,
                       s.asInstanceOf[TmVar].value.toString))
      case y => y
    }
    println(s"    $ret")
    ret
  }
  def evalOne(t: Term): Term = {
    println(t)
    t match {
      case TmApply(lambda: TmAbs, v: TmVar) =>
        println("E-APPABS")
        substitution(lambda.x, lambda.t, v) // E-APPABS
      case TmApply(lambda: TmAbs, v: TmAbs) =>
        println("E-APPABS'")
        substitution(lambda.x, lambda.t, v) // E-APPABS
      case TmApply(v1: TmVar, t2) =>
        println("E-APP2")
        TmApply(v1, evalOne(t2)) // E-APP2
      case TmApply(v1: TmAbs, t2) =>
        println("E-APP2'")
        TmApply(v1, evalOne(t2)) // E-APP2
      case TmApply(t1, t2) =>
        println("E-APP1")
        TmApply(evalOne(t1), t2) // E-APP1
      case _ => t
    }
  }
  def eval(t: Term): Term = {
    val t_ = evalOne(t)
    if (t_ == t) t else eval(t_)
  }

  // variables used in companion object
  val x = TmVar("x")
  val y = TmVar("y")
  val z = TmVar("z")
  val a = TmVar("a")
  val b = TmVar("b")
  val c = TmVar("c")
  val d = TmVar("d")
  val p = TmVar("p")
  val f = TmVar("f")
  val m = TmVar("m")
  val n = TmVar("n")
  val t = TmVar("t")

  // if-else
  val tru = lambda(x, y, x)
  val fls = lambda(x, y, y)
  val test = lambda(b, m, n, b(m)(n))

  // pair
  val pair = lambda(a, b, x, test(x)(a)(b))
  val fst = lambda(p, p(tru))
  val snd = lambda(p, p(fls))

  // charch number
  val s = TmVar("s")

  val c0 = lambda(s, z, z)
  val c1 = lambda(s, z, s(z))
  val c2 = lambda(s, z, s(s(z)))
  val c3 = lambda(s, z, s(s(s(z))))

  def realnat(charch: Term) = {
    val expr = charch(lambda(x, TmVar("x + 1")))(TmVar("0"))
      .eval()
    println(s"expr: $expr")
    val scriptManager = new javax.script.ScriptEngineManager
    val engine = scriptManager.getEngineByName("js")
    engine.eval(expr.toString)
  }

  val succ = lambda(n, s, z, s(n(s)(z)))
  val plus = lambda(n, m, s, z, n(s)(m(s)(z)))
  val times = lambda(n, m, n(plus(m))(c0))
  //λn.λs.λz.n (λx.λy. y (x s)) (λx.z) (λx.x)
  val pred =
    lambda(n,
           s,
           z,
           n(lambda(x, lambda(y, y(x(s)))))(lambda(x, z))(lambda(x, x)))

  // Y = λf.(λx.f (x x)) (λx.f (x x))
  val Y = lambda(f, lambda(x, f(x)(x))(lambda(x, f(x)(x))))

  // Z = λf.(λx.f (λy.x x y)) (λx.f (λy.x x y))
  val Z = lambda(
    f,
    lambda(x, f(lambda(y, x(x)(y))))(lambda(x, f(lambda(y, x(x)(y))))))

  val iszero = lambda(x, x(lambda(y, fls))(tru))

//  val fct = Z(
//    lambda(f, lambda(x, test(iszero(pred(x)))(c1)(times(x)(f(pred(x)))))))

}

object WithScalaFunction {
  // λx.t  ::  (x: Any) => t
  // t t    ::  t(t)
  implicit class DirtyAny(self: Any) {
    def apply(): Any = self match {
      case f: (Unit => Any) => f()
    }

    def apply(that: Any): Any = self match {
      case f: (Any => Any) => f(that)
    }
  }

  val tru = (x: Any) => (_: Any) => x
  val fls = (_: Any) => (y: Any) => y
  val test = (b: Any) => (m: Unit => Any) => (n: Unit => Any) => b(m)(n)()
  val and = (a: Any) => (b: Any) => a(b)(fls)
  val or = (a: Any) => (b: Any) => a(tru)(b)
  val pair = (f: Any) => (s: Any) => (b: Any) => b(f)(s)
  val fst = (p: Any) => p(tru)
  val snd = (p: Any) => p(fls)
  val c0 = (s: Any => Any) => (z: Any) => z
  val c1 = (s: Any => Any) => (z: Any) => s(z)
  val c2 = (s: Any => Any) => (z: Any) => s(s(z))
  val c3 = (s: Any => Any) => (z: Any) => s(s(s(z)))

  def realnat(x: Any) =
    x { acc: Int =>
      acc + 1
    }(0)

  val succ = (n: Any) => (s: Any) => (z: Any) => s(n(s)(z))
  val plus = (n: Any) => (m: Any) => (s: Any) => (z: Any) => n(s)(m(s)(z))
  val times = (n: Any) => (m: Any) => n(plus(m))(c0)
  //λn.λs.λz.n (λx.λy. y (x s)) (λx.z) (λx.x)
  val pred = (n: Any) =>
    (s: Any) =>
      (z: Any) =>
        n((x: Any) => (y: Any) => y(x(s)))((_: Any) => z)((x: Any) => x)

  //(λx.x x) (λx. x x)
  //val omega = ((x: Any => Any) => x(x)) { case x: (Any => Any) => x(x) }

  // Y = λf.(λx.f (x x)) (λx.f (x x))
  val y = (f: Any => Any) => ((x: Any) => x(f)(x(x)))((x: Any) => f(x(x)))

  // Z = λf.(λx.f (λy.x x y)) (λx.f (λy.x x y))
  val z = (f: Any => Any => Any) =>
    ((x: Any => Any => Any) => f((y: Any) => x(x)(y)))(
      x => f((y: Any) => x(x)(y))
  )

  val fctWithInt =
    z {
      case f: (Int => Int) => {
        case x: Int =>
          if (x - 1 == 0) 1
          else x * f(x - 1)
      }
    }

  val iszero = (x: Any) => x((_: Any) => fls)(tru)

  val fct = z(f =>
    x =>
      test(iszero(pred(x)))((_: Unit) => c1)((_: Unit) => times(x)(f(pred(x)))))

  val fib = z(f =>
    x =>
      test(iszero(pred(x)))((_: Unit) => x)((_: Unit) =>
        plus(f(pred(x)))(f(pred(pred(x))))))
}
