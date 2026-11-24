import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

/-!
# The commutation `∂_k K_c^T = K_c^T ∂_k` (assembly of `KTCommute`)

Source of record: `the November 2 reference manuscript` lines 3052-3058 (the
derivative of the localized adjoint interaction; the kernel is translation invariant).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem ktCoeffBound_abs {m : ℝ} (hm : 1 < m) {B : Fin 2 → ℝ × ℝ → ℝ} {A : ℝ}
    (h : KTCoeffBound m 0 B A) (l : Fin 2) (x : ℝ × ℝ) : |B l x| ≤ A := by
  have h0 := h l 0 le_rfl x
  rw [norm_iteratedFDeriv_zero] at h0
  have h1 : (1 : ℝ) ≤ (1 + x.2 ^ 2) ^ ((m + 1) / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg x.2]) (by linarith)
  have : ‖B l x‖ ≤ (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖B l x‖ :=
    le_mul_of_one_le_left (norm_nonneg _) h1
  rw [← Real.norm_eq_abs]
  linarith

theorem ktCommute_of (m : ℝ) (hS : KTSource) (hCD : KTCoeffDeriv) (hW : KTWeakLeibniz)
    (hI : KTWeakIBP) (hK : KerVelSmooth) (hBS : KerVelIsBS) (hT : KTTestInt) : KTCommute m := by
  intro hm c hc B A k hBs hBp hb f g χ χ₁ χ₂ hf hg hχ0 hχ1 hχ2 hfg hP hP1 hP2
  have hc0 : 0 < c := by linarith
  have hb0 : KTCoeffBound m 0 B A := fun l i hi x => hb l i (by omega) x
  obtain ⟨hdBs, hdBp, hdBb⟩ := hCD m c 0 B A k hBs hBp hb
  have hbd0 := ktCoeffBound_abs hm hb0
  have hbd1 := ktCoeffBound_abs hm hdBb
  obtain ⟨C1, -, HS1'⟩ := hS m hm c hc0 A
  have HS1 := HS1' B (fun l => (hBs l).continuous)
    (fun l x => by simpa using hb l 0 (by omega) x)
  have HS2 := HS1' (fun l => B0579.pd k (B l)) (fun l => (hdBs l).continuous)
    (fun l x => by simpa using hdBb l 0 le_rfl x)
  have hLeib : ∀ l, HasWeakCellDerivC c k (fun x => f x * (B l x : ℂ))
      (fun x => g x * (B l x : ℂ) + f x * (B0579.pd k (B l) x : ℂ)) := fun l =>
    hW m c hc0 k f g (B l) (hBs l) (hBp l) ⟨A, fun x => ⟨hbd0 l x, hbd1 l x⟩⟩ hfg hf hg
  refine ⟨fun ψ hψ => ⟨hT c m hc0 χ hχ0 _ (hψ.pd k), ?_⟩, fun ψ hψ => ?_⟩
  · have h1 := hT c m hc0 χ₁ hχ1 ψ hψ
    have h2 := hT c m hc0 χ₂ hχ2 ψ hψ
    have := h1.add h2
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp [add_mul]
  · have hψ' := hψ.pd k
    have hKj := fun j => hK c hc ψ hψ j
    have hKj' := fun j => hK c hc (B0579.pd k ψ) hψ' j
    -- integration by parts for each component
    have ibp : ∀ l : Fin 2,
        IntegrableOn (fun x => (f x * (B l x : ℂ)) * ((kerVel c (B0579.pd k ψ) x l : ℝ) : ℂ))
          (B0579.cell c) ∧
        IntegrableOn (fun x => (g x * (B l x : ℂ) + f x * (B0579.pd k (B l) x : ℂ)) *
          ((kerVel c ψ x l : ℝ) : ℂ)) (B0579.cell c) ∧
        ∫ x in B0579.cell c, (f x * (B l x : ℂ)) * ((kerVel c (B0579.pd k ψ) x l : ℝ) : ℂ) =
          -∫ x in B0579.cell c, (g x * (B l x : ℂ) + f x * (B0579.pd k (B l) x : ℂ)) *
            ((kerVel c ψ x l : ℝ) : ℂ) := by
      intro l
      have hpd : (fun x => B0579.pd k (fun y => kerVel c ψ y l) x) =
          fun x => kerVel c (B0579.pd k ψ) x l := funext fun x => (hKj l).2.1 k x
      obtain ⟨M0, hM0⟩ := (hKj l).2.2.1
      obtain ⟨M1, hM1⟩ := (hKj' l).2.2.1
      have := hI c hc0 k _ _ (fun x => kerVel c ψ x l) (hLeib l) (HS1 f hf l).1
        (((HS1 g hg l).1).add (HS2 f hf l).1) (hKj l).1 (hKj l).2.2.2
        ⟨max M0 M1, fun x => ⟨(hM0 x).trans (le_max_left _ _), by
          rw [(hKj l).2.1 k x]; exact (hM1 x).trans (le_max_right _ _)⟩⟩
      simp only [(hKj l).2.1] at this
      exact this
    have hbs := hBS c hc ψ hψ
    have hbs' := hBS c hc _ hψ'
    obtain ⟨-, e1⟩ := hP (B0579.pd k ψ) (kerVel c (B0579.pd k ψ)) hψ' hbs'
    obtain ⟨i2, e2⟩ := hP1 ψ (kerVel c ψ) hψ hbs
    obtain ⟨i3, e3⟩ := hP2 ψ (kerVel c ψ) hψ hbs
    beta_reduce at e3 i3
    have p1 : ∀ x : ℝ × ℝ, f x * ((kerVel c (B0579.pd k ψ) x 0 * B 0 x +
        kerVel c (B0579.pd k ψ) x 1 * B 1 x : ℝ) : ℂ) =
        (f x * (B 0 x : ℂ)) * ((kerVel c (B0579.pd k ψ) x 0 : ℝ) : ℂ) +
        (f x * (B 1 x : ℂ)) * ((kerVel c (B0579.pd k ψ) x 1 : ℝ) : ℂ) := by
      intro x; push_cast; ring
    have p2 : ∀ x : ℝ × ℝ,
        (g x * (B 0 x : ℂ) + f x * (B0579.pd k (B 0) x : ℂ)) * ((kerVel c ψ x 0 : ℝ) : ℂ) +
        (g x * (B 1 x : ℂ) + f x * (B0579.pd k (B 1) x : ℂ)) * ((kerVel c ψ x 1 : ℝ) : ℂ) =
        g x * ((kerVel c ψ x 0 * B 0 x + kerVel c ψ x 1 * B 1 x : ℝ) : ℂ) +
        f x * ((kerVel c ψ x 0 * B0579.pd k (B 0) x + kerVel c ψ x 1 * B0579.pd k (B 1) x : ℝ) : ℂ) := by
      intro x; push_cast; ring
    have i1 := hT c m hc0 χ₁ hχ1 ψ hψ
    have i1' := hT c m hc0 χ₂ hχ2 ψ hψ
    calc ∫ x in B0579.cell c, χ x * ((B0579.pd k ψ x : ℝ) : ℂ)
        = ∫ x in B0579.cell c, f x * ((kerVel c (B0579.pd k ψ) x 0 * B 0 x +
            kerVel c (B0579.pd k ψ) x 1 * B 1 x : ℝ) : ℂ) := e1
      _ = ∫ x in B0579.cell c, ((f x * (B 0 x : ℂ)) * ((kerVel c (B0579.pd k ψ) x 0 : ℝ) : ℂ) +
          (f x * (B 1 x : ℂ)) * ((kerVel c (B0579.pd k ψ) x 1 : ℝ) : ℂ)) := by
          simp only [p1]
      _ = (∫ x in B0579.cell c, (f x * (B 0 x : ℂ)) *
            ((kerVel c (B0579.pd k ψ) x 0 : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, (f x * (B 1 x : ℂ)) *
            ((kerVel c (B0579.pd k ψ) x 1 : ℝ) : ℂ) := integral_add (ibp 0).1 (ibp 1).1
      _ = -(∫ x in B0579.cell c, ((g x * (B 0 x : ℂ) + f x * (B0579.pd k (B 0) x : ℂ)) *
            ((kerVel c ψ x 0 : ℝ) : ℂ) + (g x * (B 1 x : ℂ) + f x * (B0579.pd k (B 1) x : ℂ)) *
            ((kerVel c ψ x 1 : ℝ) : ℂ))) := by
          rw [(ibp 0).2.2, (ibp 1).2.2, integral_add (ibp 0).2.1 (ibp 1).2.1]; ring
      _ = -(∫ x in B0579.cell c, (g x * ((kerVel c ψ x 0 * B 0 x + kerVel c ψ x 1 * B 1 x : ℝ) : ℂ) +
          f x * ((kerVel c ψ x 0 * B0579.pd k (B 0) x + kerVel c ψ x 1 * B0579.pd k (B 1) x : ℝ) : ℂ))) := by
          simp only [p2]
      _ = -((∫ x in B0579.cell c, g x * ((kerVel c ψ x 0 * B 0 x + kerVel c ψ x 1 * B 1 x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, f x * ((kerVel c ψ x 0 * B0579.pd k (B 0) x +
            kerVel c ψ x 1 * B0579.pd k (B 1) x : ℝ) : ℂ)) := by rw [integral_add i2 i3]
      _ = -((∫ x in B0579.cell c, χ₁ x * (ψ x : ℂ)) + ∫ x in B0579.cell c, χ₂ x * (ψ x : ℂ)) := by
          rw [e2, e3]
      _ = -∫ x in B0579.cell c, (χ₁ + χ₂) x * (ψ x : ℂ) := by
          rw [← integral_add i1 i1']
          simp [add_mul]

end UnforcedLeray.Short.IIIa
