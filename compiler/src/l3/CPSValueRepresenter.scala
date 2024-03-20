package l3

import l3.{ HighCPSTreeModule as H }
import l3.{ LowCPSTreeModule  as L }
import l3.{ L3Primitive as L3 }
//import l3.{ L3ValuePrimitive as L3V }
//import l3.{ L3TestPrimitive  as L3T }
import l3.{ CPSValuePrimitive as CPSV }
import l3.{ CPSTestPrimitive  as CPST }
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
    
    // Arithmetics
    // +
    case H.LetP(n: H.Name, L3.IntAdd, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree =>
      /*
      val x1 = Symbol.fresh("t")
      L.LetP(x1, CPS.XOr, Seq(apply(x), 1),
             L.LetP(n, CPS.Add, Seq(x1, 1), apply(b)))
      */
      tmpLetP(CPSV.XOr, Seq(rewrite(x), 1), {
        _x => L.LetP(n, CPSV.Add, Seq(_x, rewrite(y)), h2lVal(b))
      })
    // TODO: change (- 1) to (XOR 1) to clear LSB
    // -
    case H.LetP(n: H.Name, L3.IntSub, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree =>
      tmpLetP(CPSV.Sub, Seq(rewrite(x), rewrite(y)), {
        _x => L.LetP(n, CPSV.Add, Seq(_x, 1), h2lVal(b))
      })
    // ×
    case H.LetP(n: H.Name, L3.IntMul, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      tmpLetP(CPSV.Sub, Seq(rewrite(x), 1), {
        _x => tmpLetP(CPSV.ShiftRight, Seq(rewrite(y), 1), {
          _y => tmpLetP(CPSV.Mul, Seq(_x, _y), {
            z => L.LetP(n, CPSV.Add, Seq(z, 1), h2lVal(b))
          })
        })
      })
    }
    // ÷
    // ⟦n ÷ m⟧ = 2 × ( (⟦n⟧ - 1) / (⟦m⟧ - 1) ) + 1
    case H.LetP(n: H.Name, L3.IntDiv, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      tmpLetP(CPSV.Sub, Seq(rewrite(x), 1), {
        _x => tmpLetP(CPSV.Sub, Seq(rewrite(y), 1), {
          _y => tmpLetP(CPSV.Div, Seq(_x, _y), {
            z => tmpLetP(CPSV.Mul, Seq(z, 2), {
              z2 => L.LetP(n, CPSV.Add, Seq(z2, 1), h2lVal(b))
            })
          })
        })
      })
    }
    // %
    // ⟦n MOD m⟧ = (⟦n⟧ - 1 MOD ⟦m⟧ - 1) + 1
    case H.LetP(n: H.Name, L3.IntMod, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      tmpLetP(CPSV.Sub, Seq(rewrite(x), 1), {
        _x => tmpLetP(CPSV.Sub, Seq(rewrite(y), 1), {
          _y => tmpLetP(CPSV.Mod, Seq(_x, _y), {
            z => L.LetP(n, CPSV.Add, Seq(z, 1), h2lVal(b))
          })
        })
      })
    }
    // <<
    case H.LetP(n: H.Name, L3.IntShiftLeft, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      tmpLetP(CPSV.Sub, Seq(rewrite(x), 1), {
        _x => tmpLetP(CPSV.ShiftRight, Seq(rewrite(y), 1), { // Right-shifting ⟦y⟧ already clears LSB.
          _y => tmpLetP(CPSV.ShiftLeft, Seq(_x, _y), {
            z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b)) // equivalent to adding 1
          })
        })
      })
    }
    // >>
    case H.LetP(n: H.Name, L3.IntShiftRight, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(y), 1), {
        _y => tmpLetP(CPSV.ShiftRight, Seq(rewrite(x), _y), {
          z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b))
        })
      })
    }
    // &
    case H.LetP(n: H.Name, L3.IntBitwiseAnd, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      ???
    }
    // |
    case H.LetP(n: H.Name, L3.IntBitwiseOr, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      ???
    }
    // ^
    case H.LetP(n: H.Name, L3.IntBitwiseXOr, Seq(x: H.Atom, y: H.Atom), b: H.Body): L.Tree => {
      ???
    }
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
