package ch05.ext

sealed trait Term
final case class TmVar(value: String) extends Term {
  override def toString: String = s"`${value.toString}`"
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
  def substitution(lambda: TmAbs, s: Term): Term = {
    println(s"$lambda <- $s")

    def replace(t: Term): Term = t match {
      case v: TmVar if lambda.x == v => s
      case v: TmVar                  => v
      case TmAbs(x, t)               => TmAbs(replace(x), replace(t))
      case TmApply(t1, t2)           => TmApply(replace(t1), replace(t2))
    }

    lambda.t match {
      case v: TmVar        => replace(v)
      case TmAbs(y, t1)    => TmAbs(replace(y), replace(t1))
      case TmApply(t1, t2) => TmApply(replace(t1), replace(t2))
    }
  }
  def evalOne(t: Term): Term = {
    t match {
      case TmApply(lambda: TmAbs, s) => substitution(lambda, s)
      case TmApply(t1, t2)           => TmApply(evalOne(t1), t2)
      case _                         => throw new NoRuleAppliesException(t)
    }
  }
  def eval(t: Term): Term =
    try {
      eval(evalOne(t))
    } catch {
      case _: NoRuleAppliesException => t
    }
  def tmLambda2(x: Term, y: Term, t: Term): TmAbs = {
    lambda(x, lambda(y, t))
  }
  def tmLambda3(x: Term, y: Term, z: Term, t: Term): TmAbs = {
    lambda(x, tmLambda2(y, z, t))
  }
  def tmApply3(s: Term, t: Term, u: Term): Term = {
    TmApply(TmApply(s, t), u)
  }
  def tmApply4(s: Term, t: Term, u: Term, v: Term): Term = {
    tmApply3(TmApply(s, t), u, v)
//    TmApply(TmApply(TmApply(s, t), u), v)
  }
  // variables used in companion object
  val x = TmVar("x")
  val y = TmVar("y")
  val p = TmVar("p")
  val f = TmVar("f")
  val m = TmVar("m")
  val n = TmVar("n")

  // if-else
  val tru = tmLambda2(x, y, x)
  val fal = tmLambda2(x, y, y)
  def test(u: Term, v: Term, w: Term): Term = tmApply3(u, v, w)

  // pair
  def pair(t: Term, u: Term): Term = TmAbs(x, test(x, t, u))
  val fst = TmAbs(p, TmApply(p, tru))
  val snd = TmAbs(p, TmApply(p, fal))

  // charch number
  val s = TmVar("s")
  val z = TmVar("z")

  val zero = tmLambda2(s, z, z)
  val one = tmLambda2(s, z, TmApply(s, z))
  val two = tmLambda2(s, z, TmApply(s, TmApply(s, z)))
  val three = tmLambda2(s, z, TmApply(s, TmApply(z, TmApply(s, z))))
  val four = tmLambda2(s, z, TmApply(s, TmApply(s, TmApply(z, TmApply(s, z)))))

  def mult: Term = tmLambda2(m, n, TmApply(m, TmApply(n, f)))
  def pred: Term = {
    val g = TmVar("g")
    val h = TmVar("h")
    val u = TmVar("u")
    val u2 = TmVar("u2")
    val ff = tmLambda2(g, h, TmApply(h, TmApply(g, f)))
    val xx = TmAbs(u, x)
    val yy = TmAbs(u2, u2)
    tmLambda3(m, f, x, tmApply4(m, ff, xx, yy))
  }
  def succ(n: Term): Term = {
    //val nVal = eval(tmApply3(n, f, x))
    val nVal = tmApply3(n, f, x)
    tmLambda2(f, x, TmApply(f, nVal))
  }
  def pred(n: Term): Term = TmApply(snd, n)
  def naturalNumber(n: Int): Term = {
    eval((0 until n).foldLeft[Term](zero)((t, _) => succ(t)))
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
  type B = Any => Any => Any
  val test = (b: B) => (m: Unit => Any) => (n: Unit => Any) => b(m)(n)()
  val and = (a: Any => Any => Any) =>
    (b: B) => a(b)(fls).asInstanceOf[Any => Any => Any]
  val or = (a: B) => (b: B) => a(tru)(b).asInstanceOf[Any => Any => Any]
  val pair = (f: Any) => (s: Any) => (b: B) => b(f)(s)
  type P = B => Any
  val fst = (p: P) => p(tru)
  val snd = (p: P) => p(fls)
  val c0 = (s: Any => Any) => (z: Any) => z
  val c1 = (s: Any => Any) => (z: Any) => s(z)
  val c2 = (s: Any => Any) => (z: Any) => s(s(z))
  type C = (Any => Any) => Any => Any

  def cToInt(x: Any) = x match {
    case c: C => c(_.asInstanceOf[Int] + 1)(0).asInstanceOf[Int]
  }

  val succ = (n: C) => (s: Any => Any) => (z: Any) => s(n(s)(z))
  val plus = (n: C) => (m: C) => (s: Any => Any) => (z: Any) => n(s)(m(s)(z))
  val times = (n: C) =>
    (m: C) => n(plus(m).asInstanceOf[Any => Any])(c0).asInstanceOf[C]
  //λn.λs.λz.n (λx.λy. y (x s)) (λx.z) (λx.x)
  val pred = (n: C) =>
    (s: Any => Any) =>
      (z: Any) =>
        n((x: Any) => (y: Any) => y(x(s)))((_: Any) => z)((x: Any) => x)

  //(λx.x x) (λx. x x)
  //val omega = ((x: Any => Any) => x(x)) { case x: (Any => Any) => x(x) }

  // Y = λf.(λx.f (x x)) (λx.f (x x))
  val y = (f: Any => Any => Any) =>
    ((x: Any => Any => Any) => x(f)(x(x)))(x => f(x(x)))

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

  val iszero = (x: C) => x(_ => fls)(tru)

  val fct = z(f =>
    x =>
      test(iszero(pred(x)))((_: Any) => c1)((_: Any) => times(x)(f(pred(x)))))
}
