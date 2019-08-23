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

object Test {
  val tru = (x: Any) => (y: Any) => x
  val fal = (x: Any) => (y: Any) => y
  val test = (b: Any => Any => Any) => (m: Any) => (n: Any) => b(m)(n)
  val pair: Any => Any => (Any => Any => Any) => Any = (f: Any) =>
    (s: Any) => (b: Any => Any => Any) => b(f)(s)

}
