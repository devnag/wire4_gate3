import Proof.Quartic.StagePrintTuple.SetupContract

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup.BankLayout

variable {widthTapes rowTapes coefficientTapes : ℕ}

def setupNS (widthTapes rowTapes coefficientTapes : ℕ) : ℕ :=23+widthTapes+rowTapes+2*coefficientTapes

def setupNR : ℕ :=8

/-- `lem:print`, paper/paper.tex: retained source
and caches have fixed private slots outside all one-shot helper banks. -/
def dataTape (i : Fin 24) : Fin (setupNS widthTapes rowTapes coefficientTapes+1) := ⟨i.val,by
  have hi:=i.isLt
  unfold setupNS
  omega⟩

def loaderBank (i : Fin 14) : Fin (setupNS widthTapes rowTapes coefficientTapes+1) :=
  dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) ⟨i.val,by have hi:=i.isLt;omega⟩

def contextPair : Fin 2↪Fin (setupNS widthTapes rowTapes coefficientTapes+1) :=
  ⟨![dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) 4,dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) 14],by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · have hh:=congrArg Fin.val he
      norm_num [dataTape] at hh
    · have hh:=congrArg Fin.val he
      norm_num [dataTape] at hh
    · rfl⟩

/-- `lem:print`, paper/paper.tex: every small
cold helper has a genuinely disjoint fixed tape bank, used exactly once. -/
def widthBank (i : Fin widthTapes) : Fin (setupNS widthTapes rowTapes coefficientTapes+1) :=
  ⟨24+i.val,by have hi:=i.isLt;unfold setupNS;omega⟩

def rowBank (i : Fin rowTapes) : Fin (setupNS widthTapes rowTapes coefficientTapes+1) :=
  ⟨24+widthTapes+i.val,by have hi:=i.isLt;unfold setupNS;omega⟩

def zeroBank (i : Fin coefficientTapes) : Fin (setupNS widthTapes rowTapes coefficientTapes+1) :=
  ⟨24+widthTapes+rowTapes+i.val,by have hi:=i.isLt;unfold setupNS;omega⟩

def twoBank (i : Fin coefficientTapes) : Fin (setupNS widthTapes rowTapes coefficientTapes+1) :=
  ⟨24+widthTapes+rowTapes+coefficientTapes+i.val,by have hi:=i.isLt;unfold setupNS;omega⟩

theorem dataTape_injective : Function.Injective (dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)) := by
  intro i j he
  have hv:=congrArg Fin.val he
  exact Fin.ext hv

theorem loaderBank_injective : Function.Injective (loaderBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)) := by
  intro i j he
  have hv:=congrArg Fin.val he
  exact Fin.ext hv

theorem widthBank_injective : Function.Injective (widthBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)) := by
  intro i j he
  have hh:=congrArg Fin.val he
  change 24+i.val=24+j.val at hh
  exact Fin.ext (by omega)

theorem rowBank_injective : Function.Injective (rowBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)) := by
  intro i j he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+i.val=24+widthTapes+j.val at hh
  exact Fin.ext (by omega)

theorem zeroBank_injective : Function.Injective (zeroBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)) := by
  intro i j he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+rowTapes+i.val=24+widthTapes+rowTapes+j.val at hh
  exact Fin.ext (by omega)

theorem twoBank_injective : Function.Injective (twoBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)) := by
  intro i j he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+rowTapes+coefficientTapes+i.val=
    24+widthTapes+rowTapes+coefficientTapes+j.val at hh
  exact Fin.ext (by omega)

theorem widthBank_ne_data (i : Fin widthTapes) (j : Fin 24) : widthBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) i≠dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+i.val=j.val at hh
  have hj:=j.isLt
  omega

theorem rowBank_ne_data (i : Fin rowTapes) (j : Fin 24) : rowBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) i≠dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+i.val=j.val at hh
  have hj:=j.isLt
  omega

theorem zeroBank_ne_data (i : Fin coefficientTapes) (j : Fin 24) : zeroBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) i≠dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+rowTapes+i.val=j.val at hh
  have hj:=j.isLt
  omega

theorem twoBank_ne_data (i : Fin coefficientTapes) (j : Fin 24) : twoBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) i≠dataTape (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes) j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+rowTapes+coefficientTapes+i.val=j.val at hh
  have hj:=j.isLt
  omega


end NearQuarticWires.StageTupleSetup.BankLayout
