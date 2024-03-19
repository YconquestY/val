package l3

import l3.{ HighCPSTreeModule as H }
import l3.{ LowCPSTreeModule  as L }
import l3.{ L3Primitive as L3 }
import l3.{ L3ValuePrimitive as CPS }
import l3.{ L3TestPrimitive as CPST }
import CL3Literal._

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree =
    h2lVal(tree)

  private def h2lVal(tree: H.Tree): L.Tree = tree match {
    case H.LetC(cnts: Seq[H.Cnt], body: H.Body) =>
      L.LetC(cnts.map {
          case H.Cnt(name, args, e) =>
            L.Cnt(name, args, h2lVal(e))
          //case _ =>
          //  throw new Exception("Arugment is not continuation!")
      }, h2lVal(body))
    case H.AppC(cnt: H.Name, args: Seq[H.Atom]) =>
      L.AppC(cnt, args.map(rewrite))
    
    // Functions translation ignored for now
    case H.LetF(funs: Seq[H.Fun], body: H.Body) =>
      L.LetF(funs.map {
          case H.Fun(name, retC, args, e) =>
            L.Fun(name, retC, args, h2lVal(e))
          //case _ =>
          //  throw new Exception("Arugment is not function!")
      }, h2lVal(body))
    case H.AppF(fun: H.Name, retC: H.Name, args: Seq[H.Atom]) =>
      L.AppF(rewrite(fun), retC, args.map(rewrite))
    
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
    case n: H.Name     => n // ???
    case IntLit(v)     => (v.toInt << 1) | 1 // equivalent to `v * 2 + 1`
    case CharLit(c)    => (c.toInt << 3) | 6 // 0b110
    case BooleanLit(b) => if (b) 0x1A else 0xA
    case UnitLit       => 0x2
  }

  private def tmpLetP(p: L.ValuePrimitive, args: Seq[L.Atom],
                      body: L.Name => L.Tree): L.Tree = {
    val tmp = Symbol.fresh("t")
    L.LetP(tmp, p, args, body(tmp))
  }

  //private def h2lFun
}
