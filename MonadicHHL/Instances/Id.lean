import MonadicHHL.HHLMonads
import MonadicHHL.HHLWithVal

instance : HHL Id where
  elemType := Id
  relWith f p p' := p' = f p
  bind_rel := by
    aesop

instance : HHLWithValLawful Id where
  mapElem f := f
  getVal := some
  coerce σ h := by contradiction
  -- getVal_mapElem f σ := rfl
  inactive C σ σ' h := by contradiction
  active_congr h C D σ' hcd := by
    simp [HHL.relWith]
    aesop
