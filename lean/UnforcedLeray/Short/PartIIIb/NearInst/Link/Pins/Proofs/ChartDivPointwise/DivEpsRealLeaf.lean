import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.CompSmoothLeaf

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The complex derivative of the embedding `ℝ → ℂ` of a real function, in direction `v`. -/
theorem fderivOfRealLeaf {A : Chart → ℝ} {p : Chart} (hA : DifferentiableAt ℝ A p)
    (v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fun x : Chart => ((A x : ℝ) : ℂ)) p v = ((fderiv ℝ A p v : ℝ) : ℂ) := by
  have hd : HasFDerivAt (fun x : Chart => ((A x : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ A p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p hA.hasFDerivAt
  rw [hd.fderiv]
  simp

theorem pdQOfRealLeaf {A : Chart → ℝ} {p : Chart} (hA : DifferentiableAt ℝ A p) :
    UnforcedLeray.Short.PartIIa.pdQ (fun x : Chart => ((A x : ℝ) : ℂ)) p =
      ((Axi.dQ A p : ℝ) : ℂ) :=
  fderivOfRealLeaf hA (0, (1, 0))

theorem pdSOfRealLeaf {A : Chart → ℝ} {p : Chart} (hA : DifferentiableAt ℝ A p) :
    UnforcedLeray.Short.PartIIa.pdS (fun x : Chart => ((A x : ℝ) : ℂ)) p =
      ((Axi.dS A p : ℝ) : ℂ) :=
  fderivOfRealLeaf hA (1, (0, 0))

theorem pdEtaOfRealLeaf {A : Chart → ℝ} {p : Chart} (hA : DifferentiableAt ℝ A p) :
    UnforcedLeray.Short.PartIIa.pdEta (fun x : Chart => ((A x : ℝ) : ℂ)) p =
      ((Axi.dEta A p : ℝ) : ℂ) :=
  fderivOfRealLeaf hA (0, (0, 1))

theorem divEpsRealLeaf : DivEpsRealLeaf := by
  intro c ε M hM p
  have hc := compSmoothLeaf c M hM
  obtain ⟨hA1, -⟩ := hc (cmpA M) (by simp)
  obtain ⟨hB1, -⟩ := hc (cmpB M) (by simp)
  obtain ⟨hC1, -⟩ := hc (cmpC M) (by simp)
  obtain ⟨hD1, -⟩ := hc (cmpD M) (by simp)
  have dA : DifferentiableAt ℝ (cmpA M) p := (hA1.differentiable (by simp)) p
  have dB : DifferentiableAt ℝ (cmpB M) p := (hB1.differentiable (by simp)) p
  have dC : DifferentiableAt ℝ (cmpC M) p := (hC1.differentiable (by simp)) p
  have dD : DifferentiableAt ℝ (cmpD M) p := (hD1.differentiable (by simp)) p
  have tA : ∀ x : Chart, tv4 (M x) 0 = ((cmpA M x : ℝ) : ℂ) := fun x => by
    simp [tv4, cmpA]
  have tB : ∀ x : Chart, tv4 (M x) 1 = ((cmpB M x : ℝ) : ℂ) := fun x => by
    simp [tv4, cmpB]
  have tC : ∀ x : Chart, tv4 (M x) 2 = ((cmpC M x : ℝ) : ℂ) := fun x => by
    simp [tv4, cmpC]
  have tD : ∀ x : Chart, tv4 (M x) 3 = ((cmpD M x : ℝ) : ℂ) := fun x => by
    simp [tv4, cmpD]
  have qA := pdQOfRealLeaf dA
  have sA := pdSOfRealLeaf dA
  have eA := pdEtaOfRealLeaf dA
  have qB := pdQOfRealLeaf dB
  have sB := pdSOfRealLeaf dB
  have eB := pdEtaOfRealLeaf dB
  have eC := pdEtaOfRealLeaf dC
  ext i
  fin_cases i
  · simp only [merC, G0, UnforcedLeray.Short.PartIIa.divEps, UnforcedLeray.Short.PartIIa.opQ,
      UnforcedLeray.Short.PartIIa.opK, UnforcedLeray.Short.PartIIa.opS, tA, tB, tC, tD,
      qA, sA, eA, qB, sB, eB, eC, PiLp.smul_apply, smul_eq_mul, Complex.real_smul,
      PiLp.toLp_apply, Fin.isValue]
    push_cast
    ring
  · simp only [merC, G0, UnforcedLeray.Short.PartIIa.divEps, UnforcedLeray.Short.PartIIa.opQ,
      UnforcedLeray.Short.PartIIa.opK, UnforcedLeray.Short.PartIIa.opS, tA, tB, tC, tD,
      qA, sA, eA, qB, sB, eB, eC, PiLp.smul_apply, smul_eq_mul, Complex.real_smul,
      PiLp.toLp_apply, Fin.isValue]
    push_cast
    ring

end UnforcedLeray.Short.PartIIIb.NearInst
