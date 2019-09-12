package ch05.ext

sealed trait Term
final case class TmVar(value: Any) extends Term {
  override def toString: String = s"`$value`"
}
final case class TmAbs(x: Term, t: Term) extends Term {
  override def toString: String = s"λ($x.$t)"
}
final case class TmApply(t1: Term, t2: Term) extends Term {
  override def toString: String = s"($t1 $t2)"
}

object TypelessLambda {
  def lambda(x: Term, t: Term) = TmAbs(x, t)

  implicit class RichTerm(self: Term) {
    def apply(that: => Term): Term = {
      TmApply(self, that)
    }
    def eval(): Term = {
      TypelessLambda.eval(self)
    }
  }

  final class NoRuleAppliesException(term: Term) extends RuntimeException

  // substitution [x |-> s]t defined in TaPL p. 54
  def substitution(t: Term, s: Term): Term = {
    println(s"substitution: $t <- $s")

    t match {
      case TmAbs(x, TmAbs(y, t1)) if x != y =>
        TmAbs(y, substitution(t1, s))
      case TmAbs(_, TmApply(t1: TmAbs, t2: TmAbs)) =>
        TmApply(substitution(t1, s), substitution(t2, s))
      case TmAbs(x, y) if x == y => s
      case TmAbs(_, y)           => y
      case y                     => y
    }
  }
  def evalOne(t: Term): Term = {
    t match {
      case TmApply(v1: TmVar, t2)    => TmApply(v1, evalOne(t2)) // E-APP2
      case TmApply(lambda: TmAbs, s) => substitution(lambda, s) // E-APPABS
      case TmApply(t1, t2)           => TmApply(evalOne(t1), t2) // E-APP1
      case _                         => throw new NoRuleAppliesException(t)
    }
  }
  def eval(t: Term): Term =
    try {
      println(t)
      eval(evalOne(t))
    } catch {
      case _: NoRuleAppliesException => t
    }
  def lambda2(x: Term, y: Term, t: Term): TmAbs = {
    lambda(x, lambda(y, t))
  }
  def lambda3(x: Term, y: Term, z: Term, t: Term): TmAbs = {
    lambda(x, lambda2(y, z, t))
  }
  def apply2(s: Term, t: Term, u: Term): Term = {
    TmApply(TmApply(s, t), u)
  }
  def apply3(s: Term, t: Term, u: Term, v: Term): Term = {
    apply2(TmApply(s, t), u, v)
//    TmApply(TmApply(TmApply(s, t), u), v)
  }
  // variables used in companion object
  val x = TmVar("x")
  val y = TmVar("y")
  val p = TmVar("p")
  val f = TmVar("f")
  val m = TmVar("m")
  val n = TmVar("n")
  val t = TmVar("t")

  // if-else
  val tru = lambda2(x, y, x)
  val fal = lambda2(x, y, y)
  def test(u: Term, v: Term, w: Term): Term = apply2(u, v, w)

  // pair
  def pair(t: Term, u: Term): Term = TmAbs(x, test(x, t, u))
  val fst = TmAbs(p, TmApply(p, tru))
  val snd = TmAbs(p, TmApply(p, fal))

  // charch number
  val s = TmVar("s")
  val z = TmVar("z")

  val c0 = lambda2(s, z, z)
  val c1 = lambda2(s, z, s(z))
  val c2 = lambda2(s, z, s(s(z)))
  val c3 = lambda2(s, z, s(s(s(z))))

  def mult: Term = lambda2(m, n, TmApply(m, TmApply(n, f)))
  def pred: Term = {
    val g = TmVar("g")
    val h = TmVar("h")
    val u = TmVar("u")
    val u2 = TmVar("u2")
    val ff = lambda2(g, h, TmApply(h, TmApply(g, f)))
    val xx = TmAbs(u, x)
    val yy = TmAbs(u2, u2)
    lambda3(m, f, x, apply3(m, ff, xx, yy))
  }
  def succ(n: Term): Term = {
    //val nVal = eval(tmApply3(n, f, x))
    val nVal = apply2(n, f, x)
    lambda2(f, x, TmApply(f, nVal))
  }
  def pred(n: Term): Term = TmApply(snd, n)
  def naturalNumber(n: Int): Term = {
    eval((0 until n).foldLeft[Term](c0)((t, _) => succ(t)))
  }

  // fixed point combinator
  val Y = {
    val fx1 = TmAbs(x, TmApply(f, TmApply(x, x)))
    val fx2 = TmAbs(x, TmApply(f, TmApply(x, x)))
    TmAbs(f, TmApply(fx1, fx2))
  }

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

  def realnat(x: Any) =
    x { acc: Int =>
      acc + 1
    }(0)

  val succ = (n: Any) => (s: Any => Any) => (z: Any) => s(n(s)(z))
  val plus = (n: Any) =>
    (m: Any) => (s: Any => Any) => (z: Any) => n(s)(m(s)(z))
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
    (x: Any) =>
      test(iszero(pred(x)))((_: Unit) => c1)((_: Unit) => times(x)(f(pred(x)))))
}
