package l3

import l3.{ HighCPSTreeModule as H}
import l3.{ LowCPSTreeModule  as L }

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree = tree match {
    // better enclose pattern matching with a new function
    case H.LetP(n, L3.IntAdd, Seq(x, y), b) =>
      val x1 = Symbol.fresh("t")
      /*
      L.LetP(x1, CPS.XOr, Seq(apply(x), 1),
             L.LetP(n, CPS.Add, Seq(x1, 1), apply(b)))
      */
      tmpLetP(CPS.XOr, Seq(rewrite(x), 1), {
        x1 => L.LetP(n, CPS.Add, Seq(x1, rewrite(y)), apply(b))
      })
    // TODO
  }

  private def rewrite(a: H.Atom): L.Atom = a match {
    case n: H.Name => n
    case H.IntLit(v) => (v.toInt << 1) | 1 // equivalent to `v * 2 + 1`
    // TODO
  }

  private def tmpLetP(p: L.ValuePrimitive, args: Seq[L.Atom],
                      body: L.Name => L.Tree): L.Tree = {
    val tmp = Symbol.fresh("t")
    L.LetP(tmp, p, args, body(tmp))
  }
}
