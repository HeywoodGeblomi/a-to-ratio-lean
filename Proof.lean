import Statement
/-! Proof v1 (Lucas). Imports the frozen Statement.lean unchanged. Plain `decide`, no native_decide. -/
namespace ToyGeodesic

theorem toyTwoTorus_thisGeodesic_growthTwoToOne : ToyTwoTorus_ThisGeodesic_GrowthTwoToOne := by
  unfold ToyTwoTorus_ThisGeodesic_GrowthTwoToOne Z3.Gt Z3.Pos
  decide

theorem toyTwoTorus_thisGeodesic_aTie : ToyTwoTorus_ThisGeodesic_ATie := by
  unfold ToyTwoTorus_ThisGeodesic_ATie
  decide

end ToyGeodesic
