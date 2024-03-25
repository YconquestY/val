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
    case H.LetP(n: H.Name, L3.IntAdd, Seq(x: H.Atom, y: H.Atom), b: H.Body) =>
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
    case H.LetP(n: H.Name, L3.IntSub, Seq(x: H.Atom, y: H.Atom), b: H.Body) =>
      tmpLetP(CPSV.Sub, Seq(rewrite(x), rewrite(y)), {
        _x => L.LetP(n, CPSV.Add, Seq(_x, 1), h2lVal(b))
      })
    // ×
    case H.LetP(n: H.Name, L3.IntMul, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
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
    case H.LetP(n: H.Name, L3.IntDiv, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
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
    case H.LetP(n: H.Name, L3.IntMod, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
      tmpLetP(CPSV.Sub, Seq(rewrite(x), 1), {
        _x => tmpLetP(CPSV.Sub, Seq(rewrite(y), 1), {
          _y => tmpLetP(CPSV.Mod, Seq(_x, _y), {
            z => L.LetP(n, CPSV.Add, Seq(z, 1), h2lVal(b))
          })
        })
      })
    }
    // <<
    case H.LetP(n: H.Name, L3.IntShiftLeft, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
      tmpLetP(CPSV.Sub, Seq(rewrite(x), 1), {
        _x => tmpLetP(CPSV.ShiftRight, Seq(rewrite(y), 1), { // Right-shifting ⟦y⟧ already clears LSB.
          _y => tmpLetP(CPSV.ShiftLeft, Seq(_x, _y), {
            z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b)) // equivalent to adding 1
          })
        })
      })
    }
    // >>
    case H.LetP(n: H.Name, L3.IntShiftRight, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(y), 1), {
        _y => tmpLetP(CPSV.ShiftRight, Seq(rewrite(x), _y), {
          z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b))
        })
      })
    }
    // &
    case H.LetP(n: H.Name, L3.IntBitwiseAnd, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
      L.LetP(n, CPSV.And, Seq(rewrite(x), rewrite(y)), h2lVal(b))
    }
    // |
    case H.LetP(n: H.Name, L3.IntBitwiseOr, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
      L.LetP(n, CPSV.Or, Seq(rewrite(x), rewrite(y)), h2lVal(b))
    }
    // ^
    case H.LetP(n: H.Name, L3.IntBitwiseXOr, Seq(x: H.Atom, y: H.Atom), b: H.Body) => {
      tmpLetP(CPSV.XOr, Seq(rewrite(x), rewrite(y)), {
        z => L.LetP(n, CPSV.Or, Seq(z, 1), h2lVal(b))
      })
    }
    // id
    case H.LetP(n: H.Name, L3.Id, Seq(a: H.Atom), b: H.Body) => {
      L.LetP(n, CPSV.Id, Seq(rewrite(a)), h2lVal(b))
    }
    // Comparison
    // <
    case H.If(L3.IntLt, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) =>
      L.If(CPST.Lt, args.map(rewrite(_)), thenC, elseC)
    // ≤
    case H.If(L3.IntLe, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) =>
      L.If(CPST.Le, args.map(rewrite(_)), thenC, elseC)
    // =
    case H.If(L3.Eq, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) =>
      L.If(CPST.Eq, args.map(rewrite(_)), thenC, elseC)
    // Type check
    // int?
    case H.If(L3.IntP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
      tmpLetP(CPSV.And, Seq(rewrite(a), 1), {
        t1 => L.If(CPST.Eq, Seq(t1, 1), thenC, elseC)
      })
    // block?
    case H.If(L3.BlockP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
      tmpLetP(CPSV.And, Seq(rewrite(a), 0x3), {
        t1 => L.If(CPST.Eq, Seq(t1, 0), thenC, elseC)
      })
    // char?
    case H.If(L3.CharP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
      tmpLetP(CPSV.And, Seq(rewrite(a), 0x7), {
        t1 => L.If(CPST.Eq, Seq(t1, 6), thenC, elseC)
      })
    // bool?
    case H.If(L3.BoolP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) => 
      tmpLetP(CPSV.And, Seq(rewrite(a), 0xF), {
        t1 => L.If(CPST.Eq, Seq(t1, 10), thenC, elseC)
      })
    // unit?
    case H.If(L3.UnitP, Seq(a: H.Atom), thenC: H.Name, elseC: H.Name) =>
      tmpLetP(CPSV.And, Seq(rewrite(a), 0xF), {
        t1 => L.If(CPST.Eq, Seq(t1, 2), thenC, elseC)
      })
    // block operations
    // block-alloc
    case H.LetP(n: H.Name, L3.BlockAlloc, Seq(a1, a2), body: H.Body) => {
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(a1), 1), {
        t1 => tmpLetP(CPSV.ShiftRight, Seq(rewrite(a2), 1), {
          t2 => L.LetP(n, CPSV.BlockAlloc, Seq(t1, t2), h2lVal(body))
        })
      })
    }
    // block-tag
    case H.LetP(n: H.Name, L3.BlockTag, Seq(a: H.Atom), body: H.Body) =>
      tmpLetP(CPSV.BlockTag, Seq(rewrite(a)), {
        t1 => tmpLetP(CPSV.ShiftLeft, Seq(t1, 1), {
          t2 => L.LetP(n, CPSV.Or, Seq(t2, 1), h2lVal(body))
        })
      })
    // block-length
    case H.LetP(n: H.Name, L3.BlockLength, Seq(a: H.Atom), body: H.Body) =>
      tmpLetP(CPSV.BlockLength, Seq(rewrite(a)), {
        t1 => tmpLetP(CPSV.ShiftLeft, Seq(t1, 1), {
          t2 => L.LetP(n, CPSV.Or, Seq(t2, 1), h2lVal(body))
        })
      })
    // block-get
    case H.LetP(n: H.Name, L3.BlockGet, Seq(b: H.Atom, i: H.Atom), body: H.Body) =>
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(i), 1), {
        _i => L.LetP(n, CPSV.BlockGet, Seq(rewrite(b), _i), h2lVal(body)) // need to untag returned element?
      })
    // block-set!
    case H.LetP(n: H.Name, L3.BlockSet, Seq(b: H.Atom, i: H.Atom, v: H.Atom), body: H.Body) =>
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(i), 1), {
        _i => L.LetP(n, CPSV.BlockSet, Seq(rewrite(b), _i, rewrite(v)), h2lVal(body))
      })
    // I/O
    // byte-read
    case H.LetP(n: H.Name, L3.ByteRead, Seq(), body: H.Body) =>
      tmpLetP(CPSV.ByteRead, Seq.empty[L.Atom], {
        t1 => tmpLetP(CPSV.ShiftLeft, Seq(t1, 1), {
          t2 => L.LetP(n, CPSV.Or, Seq(t2, 1), h2lVal(body))
        })
      })
    // byte-write
    case H.LetP(n: H.Name, L3.ByteWrite, Seq(a: H.Atom), body: H.Body) =>
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(a), 1), {
        t1 => L.LetP(n, CPSV.ByteWrite, Seq(t1), h2lVal(body))
      })
    // integer and character conversion
    // char->int
    case H.LetP(n: H.Name, L3.CharToInt, Seq(a: H.Atom), body: H.Body) =>
      L.LetP(n, CPSV.ShiftRight, Seq(rewrite(a), 2), h2lVal(body))
    // int->char
    case H.LetP(n: H.Name, L3.IntToChar, Seq(a: H.Atom), body: H.Body) =>
      tmpLetP(CPSV.ShiftLeft, Seq(rewrite(a), 2), {
        t1 => L.LetP(n, CPSV.Or, Seq(t1, 0x2), h2lVal(body))
      })
    // halt
    case H.Halt(arg: H.Atom) => 
      tmpLetP(CPSV.ShiftRight, Seq(rewrite(arg), 1), {
        _a => L.Halt(_a)
      })
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
