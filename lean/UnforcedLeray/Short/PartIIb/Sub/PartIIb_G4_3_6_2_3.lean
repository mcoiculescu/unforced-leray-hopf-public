import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2

/-!
# Part II-b, task `PartII-b:G4/3/6/2/3` (`RawPsiJets`): decomposition

Source of record: `the November 2 reference manuscript` (SP) 2419-2423 (jets of the
stream), 261-291 (`v = ∇^⊥ψ`, `IsTrain.stream`), 463-467 (tails).

Generic hypotheses `IsStreamPair ψ v`: `ψ`, `v` are jointly `C^∞` on `(0,∞) × ℝ²` and
`v s z = toVec (∇^⊥ ψ_s z) = (-∂_η ψ, ∂_q ψ)` for `s > 0`
(`BgRegime.train_stream_smooth`, `TrainVelSmooth`, `B0140.IsTrain.stream`).

Leaf lemmas (all true source facts, short, generic in `(ψ, v)`):
* `PsiEtaSwap`, `PsiQSwap`: `∂_η ∂_s^l ψ = ∂_s^l ∂_η ψ = -∂_s^l v₀`, `∂_q ∂_s^l ψ = ∂_s^l v₁`
  (symmetry of mixed partials);
* `PsiFirstJets`: `‖∂_q,η ψ‖ ≤ 2‖v‖`, `‖D∂_sψ‖ ≤ 2‖∂_s v‖` (operator norms on the sup-norm plane);
* `PsiD2Jet`: `‖D²ψ‖ ≤ 2‖Dv‖`;
* `PsiEtaSegment`: FTC in `η` for `∂_s^l ψ` with a sup bound on `∂_s^l v` on the segment.
Proved here: `rawPsiJets_of_lemmas` (assembly: j ≥ 1 jets directly; the jets
`(0,0),(1,0),(2,0)` by the tails for `|η| ≥ Cp/ν+2`, and by the segment bound from `η* = ±(Cp/ν+2)`
inside).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartI

/-- A stream/velocity pair on `(0,∞) × ℝ²` (SP 261-291, 397): jointly smooth, `v = ∇^⊥ψ`. -/
def IsStreamPair (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec) : Prop :=
  ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => ψ x.1 x.2) (Ioi 0 ×ˢ univ) ∧
  ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => v x.1 x.2) (Ioi 0 ×ˢ univ) ∧
  ∀ s : ℝ, 0 < s → ∀ z, v s z =
    UnforcedLeray.Train.toVec (UnforcedLeray.GaussianVortex.perpendicularGradient (ψ s) z)

/-- **Mixed-partial swap** (SP 261-291): for `s > 0`, the `η`-derivative of `∂_s^l ψ(s,(q,·))` is
`-(∂_s^l v)₀`. Proof: joint smoothness and symmetry of second derivatives
(`ContDiffAt.isSymmSndFDerivAt`), induction on `l` via `iteratedDeriv_succ`; `v₀ = -∂_ηψ` by the
stream relation (`toVec_zero`). -/
def PsiEtaSwap : Prop :=
  ∀ (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec), IsStreamPair ψ v →
    ∀ (l : ℕ) (s : ℝ), 0 < s → ∀ q t : ℝ,
      HasDerivAt (fun t' : ℝ => iteratedDeriv l (fun r => ψ r (q, t')) s)
        (-(iteratedDeriv l (fun r => v r (q, t)) s 0)) t

/-- **Mixed-partial swap in `q`** (SP 261-291): for `s > 0`, the `q`-derivative of
`∂_s^l ψ(s,(·,t))` is `(∂_s^l v)₁` (same proof as `PsiEtaSwap`; `v₁ = ∂_qψ`, `toVec_one`). -/
def PsiQSwap : Prop :=
  ∀ (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec), IsStreamPair ψ v →
    ∀ (l : ℕ) (s : ℝ), 0 < s → ∀ q t : ℝ,
      HasDerivAt (fun q' : ℝ => iteratedDeriv l (fun r => ψ r (q', t)) s)
        (iteratedDeriv l (fun r => v r (q, t)) s 1) q

/-- **Jets `j = 1`** (SP 2419-2423): `ageJet 0 1 ψ = D ψ_s` has components `(v₁, -v₀)` and
`ageJet 1 1 ψ = D ∂_sψ` has components `(∂_s v₁, -∂_s v₀)` (swap), so, on the sup-norm plane,
the operator norms are `≤ |a|+|b| ≤ 2‖·‖` of the Euclidean norms of `v`, `∂_s v`. -/
def PsiFirstJets : Prop :=
  ∀ (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec), IsStreamPair ψ v →
    ∀ s : ℝ, 0 < s → ∀ z : UnforcedLeray.Cyl.Plane,
      ‖ageJet 0 1 ψ s z‖ ≤ 2 * ‖ageJet 0 0 v s z‖ ∧
      ‖ageJet 1 1 ψ s z‖ ≤ 2 * ‖ageJet 1 0 v s z‖

/-- **Jet `(0,2)`** (SP 2419-2423): `D²ψ(h,k) = h₁ Dv₁(k) - h₂ Dv₀(k)` (differentiate
`Dψ·h = h₁ v₁ - h₂ v₀`), so `‖D²ψ‖ ≤ 2 ‖Dv‖`. -/
def PsiD2Jet : Prop :=
  ∀ (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec), IsStreamPair ψ v →
    ∀ s : ℝ, 0 < s → ∀ z : UnforcedLeray.Cyl.Plane,
      ‖ageJet 0 2 ψ s z‖ ≤ 2 * ‖ageJet 0 1 v s z‖

/-- **FTC in `η`** (SP 2419-2423), from `PsiEtaSwap`: if `‖∂_s^l v(s,(q,t))‖ ≤ B` for `t` between
`a` and `b`, then `|∂_s^l ψ(s,(q,a))| ≤ |∂_s^l ψ(s,(q,b))| + B |a-b|`
(`norm_image_sub_le_of_norm_deriv_le_segment`; `‖ageJet l 0 F‖ = ‖iteratedDeriv l _‖` by
`norm_iteratedFDeriv_zero`; a component of a vector has norm `≤` the vector's norm). -/
def PsiEtaSegment : Prop :=
  ∀ (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ)
    (v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec), IsStreamPair ψ v →
    ∀ (l : ℕ) (s : ℝ), 0 < s → ∀ q a b B : ℝ,
      (∀ t ∈ uIcc a b, ‖ageJet l 0 v s (q, t)‖ ≤ B) →
      ‖ageJet l 0 ψ s (q, a)‖ ≤ ‖ageJet l 0 ψ s (q, b)‖ + B * |a - b|

/-- Monotonicity of negative powers of `ν ≤ 1`. -/
lemma psiJets_invpow_mono {ν : ℝ} (h0 : 0 < ν) (h1 : ν ≤ 1) {n m : ℕ} (h : n ≤ m) :
    (ν ^ n)⁻¹ ≤ (ν ^ m)⁻¹ :=
  inv_anti₀ (pow_pos h0 m) (pow_le_pow_of_le_one h0.le h1 h)

/-- **Assembly of `RawPsiJets`** from the tails, the velocity jets and the four leaf lemmas. -/
theorem rawPsiJets_of_lemmas (ht : RawPsiTailJets) (hv : RawVelJets) (hS : TrainVelSmooth)
    (hF : PsiFirstJets) (hD : PsiD2Jet) (hSeg : PsiEtaSegment) : RawPsiJets := by
  intro Sig hSig dm dp hdm
  obtain ⟨Cp, hCp, ht'⟩ := ht
  obtain ⟨Ct, Nt, νt, hCt, hνt, Ht⟩ := ht' Sig hSig dm dp hdm
  obtain ⟨Cv, Nv, νv, hCv, hνv, Hv⟩ := hv Sig hSig dm dp hdm
  refine ⟨Ct + 6 * (Cp + 2) * Cv + 6 * Cv, max Nt Nv + 1, min (min νt νv) 1, by positivity,
    lt_min (lt_min hνt hνv) one_pos, ?_⟩
  intro p d hd hν hS' x hx0 hxH
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνt' : p.ν ≤ νt := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνv' : p.ν ≤ νv := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  set E : ℝ := (p.ν ^ (max Nt Nv + 1))⁻¹ with hE
  have hE1 : (p.ν ^ Nt)⁻¹ ≤ E :=
    psiJets_invpow_mono hνp hν1 ((le_max_left _ _).trans (Nat.le_succ _))
  have hE2 : (p.ν ^ Nv)⁻¹ ≤ E :=
    psiJets_invpow_mono hνp hν1 ((le_max_right _ _).trans (Nat.le_succ _))
  have hE3 : p.ν⁻¹ * (p.ν ^ Nv)⁻¹ ≤ E := by
    have : p.ν⁻¹ * (p.ν ^ Nv)⁻¹ = (p.ν ^ (Nv + 1))⁻¹ := by
      rw [pow_succ, mul_inv, mul_comm]
    rw [this]
    exact psiJets_invpow_mono hνp hν1 (Nat.succ_le_succ (le_max_right _ _))
  have hEn : 0 ≤ E := by positivity
  have hsp : IsStreamPair p.train.ψ p.train.v :=
    ⟨hd.train_stream_smooth, hS p d dm dp hd, fun s hs z => p.train.isTrain.stream s hs.le z⟩
  set Vb : ℝ := Cv * (p.ν ^ Nv)⁻¹ with hVb
  have hVbn : 0 ≤ Vb := by positivity
  have hVE : Vb ≤ Cv * E := mul_le_mul_of_nonneg_left hE2 hCv.le
  have hV : ∀ t : ℝ,
      ‖ageJet 0 0 p.train.v x.1 (x.2.1, t)‖ ≤ Vb ∧ ‖ageJet 1 0 p.train.v x.1 (x.2.1, t)‖ ≤ Vb ∧
      ‖ageJet 0 1 p.train.v x.1 (x.2.1, t)‖ ≤ Vb ∧ ‖ageJet 2 0 p.train.v x.1 (x.2.1, t)‖ ≤ Vb := by
    intro t
    have h := Hv p d hd hνv' hS' (x.1, (x.2.1, t)) hx0 hxH
    dsimp only at h
    have a0 := norm_nonneg (ageJet 0 0 p.train.v x.1 (x.2.1, t))
    have a1 := norm_nonneg (ageJet 1 0 p.train.v x.1 (x.2.1, t))
    have a2 := norm_nonneg (ageJet 0 1 p.train.v x.1 (x.2.1, t))
    have a3 := norm_nonneg (ageJet 2 0 p.train.v x.1 (x.2.1, t))
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨h01, h11⟩ := hF _ _ hsp x.1 hx0 x.2
  have h02 := hD _ _ hsp x.1 hx0 x.2
  have hv00 := (hV x.2.2).1
  have hv10 := (hV x.2.2).2.1
  have hv01 := (hV x.2.2).2.2.1
  have hx2 : (x.2.1, x.2.2) = x.2 := rfl
  rw [hx2] at hv00 hv10 hv01
  have hmain : ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
      ‖ageJet 2 0 p.train.ψ x.1 x.2‖ ≤ (Ct + 6 * (Cp + 2) * Cv) * E := by
    by_cases hcase : Cp / p.ν + 2 ≤ |x.2.2|
    · have h := Ht p d hd hνt' hS' x hx0 hxH hcase
      have : Ct * (p.ν ^ Nt)⁻¹ ≤ Ct * E := mul_le_mul_of_nonneg_left hE1 hCt.le
      have : 0 ≤ 6 * (Cp + 2) * Cv * E := by positivity
      nlinarith
    · push_neg at hcase
      set b : ℝ := Cp / p.ν + 2 with hb
      have hbpos : 0 < b := by positivity
      have hT := Ht p d hd hνt' hS' (x.1, (x.2.1, b)) hx0 hxH (by
        show Cp / p.ν + 2 ≤ |b|
        rw [abs_of_pos hbpos])
      dsimp only at hT
      have hab : |x.2.2 - b| ≤ 2 * (Cp + 2) * p.ν⁻¹ := by
        have h1 : |x.2.2 - b| ≤ |x.2.2| + |b| := abs_sub _ _
        rw [abs_of_pos hbpos] at h1
        have hinv : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνp).2 hν1
        have : Cp / p.ν = Cp * p.ν⁻¹ := div_eq_mul_inv _ _
        nlinarith
      have hseg : ∀ l : ℕ, l ∈ ({0, 1, 2} : Set ℕ) →
          ‖ageJet l 0 p.train.ψ x.1 x.2‖ ≤
            ‖ageJet l 0 p.train.ψ x.1 (x.2.1, b)‖ + Vb * |x.2.2 - b| := by
        intro l hl
        exact hSeg _ _ hsp l x.1 hx0 x.2.1 x.2.2 b Vb (by
          intro t _
          have h := hV t
          rcases hl with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.2)
      have e0 := hseg 0 (by simp)
      have e1 := hseg 1 (by simp)
      have e2 := hseg 2 (by simp)
      have hprod : Vb * |x.2.2 - b| ≤ 2 * (Cp + 2) * Cv * E := by
        calc Vb * |x.2.2 - b| ≤ Vb * (2 * (Cp + 2) * p.ν⁻¹) :=
              mul_le_mul_of_nonneg_left hab hVbn
          _ = 2 * (Cp + 2) * Cv * (p.ν⁻¹ * (p.ν ^ Nv)⁻¹) := by rw [hVb]; ring
          _ ≤ 2 * (Cp + 2) * Cv * E :=
              mul_le_mul_of_nonneg_left hE3 (by positivity)
      have : Ct * (p.ν ^ Nt)⁻¹ ≤ Ct * E := mul_le_mul_of_nonneg_left hE1 hCt.le
      nlinarith
  have hj : 2 * ‖ageJet 0 0 p.train.v x.1 x.2‖ + 2 * ‖ageJet 1 0 p.train.v x.1 x.2‖ +
      2 * ‖ageJet 0 1 p.train.v x.1 x.2‖ ≤ 6 * Cv * E := by nlinarith
  calc _ ≤ (Ct + 6 * (Cp + 2) * Cv) * E + 6 * Cv * E := by linarith
    _ = (Ct + 6 * (Cp + 2) * Cv + 6 * Cv) * (p.ν ^ (max Nt Nv + 1))⁻¹ := by rw [hE]; ring

end UnforcedLeray.Short.IIb
