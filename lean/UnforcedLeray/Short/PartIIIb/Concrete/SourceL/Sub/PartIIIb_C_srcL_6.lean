import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The outward region `{(ε r)² > 5ν/6}` in `y`-coordinates, written `{b < r²}` with `b = 5ν/(6ε²)`
(source 4776-4791: there the Newton kernel is separated from the old source disc, which lies in
`|x'|² < 5ν/6` since `χ_o(νu) = 0` for `νu ≤ 6/5`). -/
def outReg (ν ε : ℝ) : Set Vec3 := {y | 5 * ν / (6 * ε ^ 2) < cylR y ^ 2}

/-- **Sub-lemma 1** (source 4776-4782, 4917-4937): on the outward region the zero-width Newton
fields `W^mt_μ - W^mt_{μ+1}` are `C^∞`.  Proof: `newtonN` is `C^∞` off `0` with
`|D^m newtonN(w)| ≤ C_m |w|^{-1-m}`; for `x = εy` in the region and `t ∈ (0,1]`, `|x'|² < 5ν/6`
the points `x - t(x',0)` stay at distance `≥ δ > 0` from `0` locally uniformly; `∫|sigmaM| ≤ C N₀(M)
< ∞`; differentiate under the integral (dominated convergence, iterated). -/
def XSZSmooth : Prop :=
  ∀ (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < ε → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) (outReg ν ε)

/-- **Sub-lemma 2** (source 4776-4791, 4917-4937): decay of the derivatives of
`Z = W^mt_μ - W^mt_{μ+1}` away from the axis: `|D^k Z(w)| ≤ C_k (1+|w|)^{-(4+k)}` on
`{a ≤ r²}` for every `a` above the threshold `5ν/(6ε²)` (from `|D^{3+k} N(w)| ≲ |w|^{-4-k}`, the
bounded source support `|x'|² < 5ν/6`, and `∫|sigmaM| < ∞`). -/
def XSZDecay : Prop :=
  ∀ (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < ε → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M →
    ∀ a : ℝ, 5 * ν / (6 * ε ^ 2) < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
      ‖iteratedFDeriv ℝ k (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) w‖ ≤
        C * (1 + ‖w‖) ^ (-(4 + (k : ℝ)))

/-- **Sub-lemma 3** (source 4178-4186, 4917-4937): the outward primitive
`Ψ_Z(y) = -∫_{r}^∞ ρ Z_z(rayPt y ρ) dρ` is `C^∞` on `{b < r²}` when `Z` is `C^∞` there with
`|D^k Z(w)| ≤ C (1+|w|)^{-(4+k)}` on each `{a ≤ r²}`, `a > b` (differentiation under the integral
in `y`; `rayPt` is smooth for `cylR y > 0`, `D^j_y rayPt ≲ ρ^j`, so the integrand's `k`-th
derivative is `≲ ρ^{1-4}`). -/
def XSStreamPsi : Prop :=
  ∀ (b : ℝ) (Z : Vec3 → Vec3), 0 < b →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2} →
    (∀ a : ℝ, b < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
      ‖iteratedFDeriv ℝ k Z w‖ ≤ C * (1 + ‖w‖) ^ (-(4 + (k : ℝ)))) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (streamPsi Z) {y | b < cylR y ^ 2}

theorem continuous_cylR : Continuous cylR := by
  unfold cylR; fun_prop

theorem isOpen_outReg (ν ε : ℝ) : IsOpen (outReg ν ε) :=
  isOpen_lt continuous_const (continuous_cylR.pow 2)

/-- `χ_y(ν/(εr)²)` vanishes where `(εr)² < ν`. -/
theorem chiYr_zero_of_lt {ν ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hε : 0 < ε)
    {r : ℝ} (hr : (ε * r) ^ 2 < ν) : chiYr ν ε χy r = 0 := by
  unfold chiYr
  split_ifs with h0
  · rfl
  · have hpos : 0 < (ε * r) ^ 2 := by
      have : ε * r ≠ 0 := by
        intro h; apply h0
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h hε.ne'
        · exact h
      positivity
    apply hχ.zero
    rw [le_div_iff₀ hpos]; linarith

theorem chiYr_contDiffOn {ν ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hε : 0 < ε) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chiYr ν ε χy) (Ioi 0) := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ => χy (ν / (ε * r) ^ 2)) (Ioi 0) := by
    refine hχ.smooth.comp_contDiffOn ?_
    refine contDiffOn_const.div ((contDiffOn_const.mul contDiffOn_id).pow 2) ?_
    intro r hr
    have : r ≠ 0 := ne_of_gt hr
    simp [hε.ne', this]
  refine h.congr ?_
  intro r hr
  have : r ≠ 0 := ne_of_gt hr
  simp [chiYr, this]

theorem xmtSmooth_of (h1 : XSZSmooth) (h2 : XSZDecay) (h3 : XSStreamPsi) : XmtSmooth := by
  intro c ν ε μ χo χy hL M hM
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : (ε * cylR y) ^ 2 < ν
  · -- near `y` the cutoff vanishes
    have hopen : IsOpen {y' : Vec3 | (ε * cylR y') ^ 2 < ν} :=
      isOpen_lt ((continuous_const.mul continuous_cylR).pow 2) continuous_const
    have hev : ∀ᶠ y' in nhds y, Xmt c ν ε μ χo χy M y' = 0 := by
      filter_upwards [hopen.mem_nhds hy] with y' hy'
      have hz : chiYr ν ε χy (cylR y') = 0 := chiYr_zero_of_lt hL.chiY hL.eps_pos hy'
      have hd : deriv (chiYr ν ε χy) (cylR y') = 0 := by
        have hop : IsOpen {r : ℝ | (ε * r) ^ 2 < ν} :=
          isOpen_lt ((continuous_const.mul continuous_id).pow 2) continuous_const
        have : chiYr ν ε χy =ᶠ[nhds (cylR y')] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hy'] with r hr
          exact chiYr_zero_of_lt hL.chiY hL.eps_pos hr
        rw [this.deriv_eq]; simp
      simp [Xmt, streamCut, hz, hd]
    exact (contDiffAt_const (c := (0 : Vec3))).congr_of_eventuallyEq hev
  · have hν := hL.nu_pos
    have hε := hL.eps_pos
    have hyU : y ∈ outReg ν ε := by
      unfold outReg
      simp only [mem_setOf_eq]
      rw [div_lt_iff₀ (by positivity)]
      push_neg at hy
      nlinarith
    set Z : Vec3 → Vec3 := youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M with hZ
    have hb : 0 < 5 * ν / (6 * ε ^ 2) := by positivity
    have hZs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z (outReg ν ε) :=
      h1 c ν ε μ χo M hL.c_pos hν hε hL.mu_pos hL.chiO hM
    have hΨ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (streamPsi Z) (outReg ν ε) := by
      refine h3 _ Z hb hZs ?_
      intro a ha k
      exact h2 c ν ε μ χo M hL.c_pos hν hε hL.mu_pos hL.chiO hM a ha k
    have hcyl : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cylR (outReg ν ε) := by
      intro y' hy'
      have hp : 0 < y' 0 ^ 2 + y' 1 ^ 2 := by
        have := hy'
        simp only [outReg, mem_setOf_eq, cylR] at this
        have h0 : 0 ≤ y' 0 ^ 2 + y' 1 ^ 2 := by positivity
        rw [Real.sq_sqrt h0] at this
        exact lt_of_le_of_lt (by positivity) this
      refine ContDiffAt.contDiffWithinAt ?_
      unfold cylR
      refine ContDiffAt.sqrt ?_ hp.ne'
      fun_prop
    have hpos : ∀ y' ∈ outReg ν ε, 0 < cylR y' := by
      intro y' hy'
      have := hy'
      simp only [outReg, mem_setOf_eq] at this
      have hnn : 0 ≤ cylR y' := Real.sqrt_nonneg _
      rcases hnn.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at this
        have : 0 < 5 * ν / (6 * ε ^ 2) := by positivity
        simp at *; linarith
    have hmaps : Set.MapsTo cylR (outReg ν ε) (Ioi 0) := fun y' hy' => hpos y' hy'
    have hchi := (chiYr_contDiffOn (ν := ν) hL.chiY hε).comp hcyl hmaps
    have hdchi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (chiYr ν ε χy)) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1
        (chiYr_contDiffOn (ν := ν) hL.chiY hε)).2
    have hdchi' := hdchi.comp hcyl hmaps
    have hall : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Xmt c ν ε μ χo χy M) (outReg ν ε) := by
      have : Xmt c ν ε μ χo χy M = fun y' =>
          chiYr ν ε χy (cylR y') • Z y' +
            (deriv (chiYr ν ε χy) (cylR y') / cylR y' * streamPsi Z y') • (![0, 0, 1] : Vec3) := by
        rfl
      rw [this]
      refine (hchi.smul hZs).add ?_
      exact ContDiffOn.smul
        ((hdchi'.div hcyl (fun y' hy' => (hpos y' hy').ne')).mul hΨ) contDiffOn_const
    exact (hall.of_le (by
      have h7 : ((7 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
      first | exact h7 | simpa using h7 | (rw [← WithTop.coe_ofNat]; exact h7))).contDiffAt ((isOpen_outReg ν ε).mem_nhds hyU)

end UnforcedLeray.Short.PartIIIb.Concrete
