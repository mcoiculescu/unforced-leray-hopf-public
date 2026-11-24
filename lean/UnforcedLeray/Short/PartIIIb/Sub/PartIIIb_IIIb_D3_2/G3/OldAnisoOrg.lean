import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput

/-!
# `PartIII-b:IIIb-D3/2/G3/1/org`: decomposition of `G3.OldAnisoTested`

Source of record: `the November 2 reference manuscript` (73 pages):
* actual bare columns `φ_{ν,+}(s) = 𝒰(s,0)q_{+,0}`, `φ_{ν,-} = φ̄_{ν,+}` (lines 4416-4426);
* later-output operator bound `eq:young-later-output` for an arbitrary state at `H = 2/ν`
  (lines 4432-4457, from `prop:short-full-clock` 2836-2846 and `eq:ct-tested-impulse`,
  `eq:ct-absolute-impulse` 3266-3289);
* Duhamel decomposition at `H = 2/ν` and amplitude bound `|a_{ν,±}(f)| ≤ C_K ‖f‖_𝓘`
  (lines 4480-4508), unforced cocycle propagation for `s ≥ H` (lines 4509-4514);
* `eq:young-old-anisotropy` and its real form (`a_- = ā_+` for real `μ` and real forcing `g_B`,
  lines 4520-4543), used at `f = g_B` on `s ≥ u_o = ν^{-3/2}` (lines 4665-4676);
* canonical Mellin limit `eq:ct-mellin` (lines 3314-3343) and stress anisotropy `eq:ct-anisotropy`
  (lines 3392-3401).

Decomposition into four named propositions:
* `DuhamelDecomp D` (leaf `G3/1/1`, `OldAnisoDuhamel.lean`): trajectory split
  `ξ_B(s) = xiBare + xiFromH r_H` on `s ≥ 2/ν`, remainder bound `‖r_H‖ ≤ C ν |F_+(H,0)| ‖g_B‖_𝓘`,
  and amplitude bound `‖a_{ν,+}(B)‖ ≤ C ‖g_B‖_𝓘`;
* `OldReadoutLinear D` (leaf `G3/1/2`, `OldAnisoLinear.lean`): `ℝ`-linearity on `X_{m,c}` of the
  cell stress readout `ξ ↦ cellInt c (2 M_{zz} - M_{rr})` at each age `s`;
* `LaterOutputRem D` (and `LaterOutputAbsOp D` for `G1/5/2`, task `G3/1/3`, `OldAnisoRem.lean`):
  the later-output operator bound on `s ≥ u_o` for an arbitrary state `x` at `H = 2/ν`;
* `BareColUnit D` (task `G3/1/4`, `OldAnisoBare.lean`): old-output anisotropy of the two unit
  bare columns `a = 1` and `a = i` (`BareColAniso D` for arbitrary `a : ℂ` is derived here by
  `ℝ`-linearity and a uniform-in-window `ε → ω_can` extraction).

Assembly: `oldAnisoTested_of`, composed by task `PartIII-b:IIIb-D3/2/G3/1` (`OldAniso.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF

namespace G3

/-! ## 1. Concrete trajectories and functionals on `s ≥ u_o = ν^{-3/2}` -/

/-- The unforced bare column combination `a φ_+(s) + ā φ̄_+(s)`, `φ_+(s) = 𝒰(s,0)q_{+,0}`
(source 4416-4420, 4501-4505, 4540-4543). -/
def bareCol (S : FlatSetting) (a : ℂ) (s : ℝ) : S.pk.X :=
  a • S.pk.Uev s 0 (S.pk.q true 0) +
    (starRingEnd ℂ a) • S.conjX (S.pk.Uev s 0 (S.pk.q true 0))

/-- The Floquet-weighted bare column `s^{-μ}(a φ_+(s) + ā φ̄_+(s))` (source 4509-4510, 4520-4543). -/
def xiBare (S : FlatSetting) (μ : ℝ) (a : ℂ) (s : ℝ) : S.pk.X :=
  ((s : ℂ) ^ (-(μ : ℂ))) • bareCol S a s

/-- The Floquet-weighted unforced evolution `s^{-μ} 𝒰(s,H) x` from a state `x` at `H = 2/ν`
(source 4440-4455, 4509-4514). -/
def xiFromH (S : FlatSetting) (ν μ : ℝ) (x : S.pk.X) (s : ℝ) : S.pk.X :=
  ((s : ℂ) ^ (-(μ : ℂ))) • S.pk.Uev s (2 / ν) x

/-- The Duhamel remainder `r_H = H^μ ξ_B(H) - (a_+ φ_+(H) + ā_+ φ̄_+(H))` at `H = 2/ν`
(source 4501-4508, 4540-4543). -/
def duhRemH (D : SeqData) (S : FlatSetting) (n : ℕ) (z : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : S.pk.X :=
  duhamel S.pk (D.mu n z : ℂ) (S.gB B) (2 / nu D n) -
    bareCol S (S.aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B) (2 / nu D n)

/-- The old-stress functional `I_T(s ≥ u_o; Mcell(ξ))`, `u_o = ν^{-3/2}`
(source 4520-4543, 4668-4676). -/
def itOld (S : FlatSetting) (ν : ℝ) (ξ : ℝ → S.pk.X) : ℝ :=
  S.IT (fun s => if ν ^ (-(3 / 2 : ℝ)) ≤ s then S.Mcell s (ξ s) else fun _ => 0)

/-- The integrand of `itOld S ν ξ` on `(0, ∞)`. -/
def itOldDens (S : FlatSetting) (ν : ℝ) (ξ : ℝ → S.pk.X) (s : ℝ) : ℝ :=
  S.ITdens (fun s => if ν ^ (-(3 / 2 : ℝ)) ≤ s then S.Mcell s (ξ s) else fun _ => 0) s

/-- The absolute-stress moment integrand of `xiFromH S ν μ x` at order `k`
(source 4440-4457, `eq:young-later-output`). -/
def tailAbsIntegrand (S : FlatSetting) (ν μ : ℝ) (k : ℕ) (x : S.pk.X) (s : ℝ) : ℝ :=
  S.chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
    cellInt S.c (fun p => matNorm (S.Mcell s (xiFromH S ν μ x s) p))

/-- The leading term `(3π/(2c))(μ+3/2)ν^{3+2μ} Im(a N_ν J(μ))` of `eq:young-old-anisotropy`
in real form (source 4540-4543, 4668-4676). -/
def bareColLead (D : SeqData) (S : FlatSetting) (n : ℕ) (z : ℝ) (a : ℂ) : ℝ :=
  (3 * Real.pi / (2 * S.c)) * (D.mu n z + 3 / 2) * nu D n ^ (3 + 2 * D.mu n z) *
    (a * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).im

/-- The canonical old-output scale `𝒜_ν = |N_ν| ν^{3+2μ} / c` at level `n` and window point `z`
(source 4455, 4522). -/
def oldScaleA (D : SeqData) (S : FlatSetting) (n : ℕ) (z : ℝ) : ℝ :=
  ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) / S.c

/-! ## 2. Named propositions for the decomposition -/

/-- **Leaf 1 (`G3/1/1`): Duhamel decomposition on `s ≥ H = 2/ν` and amplitude bound**
(source 4489-4510, 4540-4543). For every actual flat sequence, uniformly in `z ∈ [-1,1]` and
`B ∈ 𝓑_a`:
1. for `s ≥ 2/ν`, `ξ_B(s) = xiBare a_+ s + xiFromH r_H s`;
2. `‖r_H‖ ≤ C_duh ν |F_+(H,0)| ‖g_B‖_𝓘`;
3. `‖a_{ν,+}(B)‖ ≤ C_amp ‖g_B‖_𝓘`. -/
def DuhamelDecomp (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (Cduh Camp : ℝ) (N : ℕ), 0 ≤ Cduh ∧ 0 ≤ Camp ∧
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B, IsBclass D.K.as (nu D n) B →
        (∀ s : ℝ, 2 / nu D n ≤ s →
          (S n).xi (D.mu n z : ℂ) B s =
            xiBare (S n) (D.mu n z)
              ((S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B) s +
            xiFromH (S n) (nu D n) (D.mu n z) (duhRemH D (S n) n z B) s) ∧
        ‖duhRemH D (S n) n z B‖ ≤
          Cduh * nu D n * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ *
            testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ)
              (1.1 / nu D n) ((S n).gB B) ∧
        ‖(S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B‖ ≤
          Camp * testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ)
            (1.1 / nu D n) ((S n).gB B)

/-- **Leaf 2 (`G3/1/2`): `ℝ`-linearity of the cell stress readout** (source 4610-4612, from
`kcMerLinear`, `Sub/PartIII-b_C_asrc_kflat_2_3.lean:66`, and `tr.isTrain.finite_energy`). -/
def OldReadoutLinear (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℝ, ∀ ξ ξ' : (S n).pk.X, ∀ r : ℝ,
      cellInt (S n).c (fun p =>
          2 * (S n).Mcell s (ξ + ξ') p 2 2 - (S n).Mcell s (ξ + ξ') p 0 0) =
        cellInt (S n).c (fun p => 2 * (S n).Mcell s ξ p 2 2 - (S n).Mcell s ξ p 0 0) +
        cellInt (S n).c (fun p => 2 * (S n).Mcell s ξ' p 2 2 - (S n).Mcell s ξ' p 0 0) ∧
      cellInt (S n).c (fun p =>
          2 * (S n).Mcell s ((r : ℂ) • ξ) p 2 2 - (S n).Mcell s ((r : ℂ) • ξ) p 0 0) =
        r * cellInt (S n).c (fun p => 2 * (S n).Mcell s ξ p 2 2 - (S n).Mcell s ξ p 0 0)

/-- **The later-output absolute-stress operator bound** (`eq:young-later-output`, source 4440-4457,
from `FullClockLongForward` and `eq:ct-tested-impulse` / `eq:ct-absolute-impulse` 3272-3289):
for every actual flat sequence, uniformly for large `n`, `k ≤ 1`, `z ∈ [-1,1]` and every state
`x ∈ X_{m,c}` at `H = 2/ν`, the unforced evolution `s^{-μ} 𝒰(s,H) x` has integrable absolute-stress
density on `(2/ν, ∞)` and its integral is at most `C 𝒜_ν ν^k |F_+(H,0)|⁻¹ ‖x‖`.
Shared with `G1.LaterOutput.TailBound` (`tailBound_of_laterOutputAbsOp` below). -/
def LaterOutputAbsOp (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ x : (S n).pk.X,
        IntegrableOn (tailAbsIntegrand (S n) (nu D n) (D.mu n z) k x) (Ioi (2 / nu D n)) ∧
        ∫ s in Ioi (2 / nu D n), tailAbsIntegrand (S n) (nu D n) (D.mu n z) k x s ≤
          C * oldScaleA D (S n) n z * nu D n ^ k *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖x‖)

/-- **Leaf 3 (`G3/1/3`): the later-output tested-stress operator bound on `s ≥ u_o = ν^{-3/2}`**
(`eq:young-later-output`, source 4440-4457, 4509-4514): for every actual flat sequence, uniformly
for large `n`, `z ∈ [-1,1]` and every state `x ∈ X_{m,c}` at `H = 2/ν`, `itOldDens` of
`s^{-μ} 𝒰(s,H) x` is integrable on `(0, ∞)` and
`|I_T(s ≥ u_o; Mcell(s^{-μ} 𝒰(s,H) x))| ≤ C 𝒜_ν |F_+(H,0)|⁻¹ ‖x‖`. -/
def LaterOutputRem (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ x : (S n).pk.X,
      Integrable (itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x))
        (volume.restrict (Ioi (0 : ℝ))) ∧
      |itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) x)| ≤
        C * oldScaleA D (S n) n z *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖x‖)

/-- **Combined canonical Mellin and stress anisotropy** (source 3314-3343 `eq:ct-mellin` and
3392-3401 `eq:ct-anisotropy`; proved below in `ctAnisoMellin_of` from `IIIa.CTMellin` and
`IIIa.CTAnisotropy`). -/
def CTAnisoMellin : Prop :=
  ∀ P : UnforcedLeray.Blueprint.Planar.PlanarData,
    UnforcedLeray.Blueprint.Planar.IsPlanarReference P →
    ∀ m : ℝ, 8 < m → ∀ K : Set ℂ, IIIa.IsAdmissibleK K →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (IIIa.preparedDatum P ν) w u →
          ∀ μ ∈ K,
            IntegrableOn (fun s => (2 * IIIa.pairQ tr μ (u s) s - IIIa.pairEta tr μ (u s) s) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (IIIa.onsetAge ν)) ∧
              ‖(∫ s in Ioi (IIIa.onsetAge ν), (2 * IIIa.pairQ tr μ (u s) s -
                  IIIa.pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
                3 * Complex.I * (μ + 3 / 2) *
                  (-((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν /
                    (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) * (ν : ℂ) ^ (3 + 2 * μ)) *
                  IIIa.mellinJc P μ‖ ≤ ε * IIIa.scaleA P ν μ

/-- **Leaf 4 (`G3/1/4`): old-output anisotropy of the two unit bare columns `a = 1` and `a = i`**
(source 4416-4426, 4520-4543, from `CTAnisoMellin` after identifying `φ_+(s) = 𝒰(s,0)q_{+,0}`
with the column from `IIIa.preparedDatum`). -/
def BareColUnit (D : SeqData) : Prop :=
  ForActual D fun S =>
    (∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      Integrable (itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) 1))
        (volume.restrict (Ioi (0 : ℝ))) ∧
      Integrable (itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I))
        (volume.restrict (Ioi (0 : ℝ)))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) - bareColLead D (S n) n z 1| ≤
        ε * oldScaleA D (S n) n z ∧
      |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
          bareColLead D (S n) n z Complex.I| ≤
        ε * oldScaleA D (S n) n z)

/-- **Old-output anisotropy of the bare column for arbitrary `a : ℂ`** (source 4520-4543;
proved below in `bareColAniso_of_unit` from `OldReadoutLinear` and `BareColUnit`). -/
def BareColAniso (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (ωcan : ℕ → ℝ) (C : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧ (∀ n, 0 ≤ ωcan n) ∧ 0 ≤ C ∧
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ a : ℂ,
        Integrable (itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) a))
          (volume.restrict (Ioi (0 : ℝ))) ∧
        |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) a) - bareColLead D (S n) n z a| ≤
          C * (oldScaleA D (S n) n z * ωcan n) * ‖a‖

/-! ## 3. Helper lemmas for `G3/1/1` (Duhamel, conjugation, cocycle, amplitudes) -/

/-- `F_-(s,t) = conj F_+(s,t)` for `0 < ν` and `s, t ≥ 0` (source 4368-4372). -/
theorem fpm_false_eq_conj {lam κ : ℂ} {ν s t : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Fpm false lam κ ν s t = conj (Fpm true lam κ ν s t) := by
  have hr : 0 < aOf ν s / aOf ν t :=
    div_pos (aOf_pos_of_nonneg ν s hν hs) (aOf_pos_of_nonneg ν t hν ht)
  have harg : Complex.arg ((aOf ν s / aOf ν t : ℝ) : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  rw [fpm_false_eq, fpm_true_eq, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- For real `μ` and a real forcing (`conjX (f t) = f t`), `a_{ν,-}(f) = conj (a_{ν,+}(f))`
(source 4540-4543). -/
theorem aFrozen_false_eq_conj_of_real {pk : YoungPkg} {conjX : pk.X → pk.X}
    (hL : YoungLaws pk conjX) {lam κ : ℂ} {ν μ Tf : ℝ} (hν : 0 < ν)
    {f : ℝ → pk.X} (hf : ∀ t, conjX (f t) = f t) :
    aFrozen pk false lam κ ν (μ : ℂ) Tf f = conj (aFrozen pk true lam κ ν (μ : ℂ) Tf f) := by
  unfold aFrozen
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [map_mul, map_mul, map_inv₀, FlatSettingInst.conj_cpow_real ht.1,
    fpm_false_eq_conj hν ht.1.le le_rfl, hL.conj_ell, hf t]

/-- Amplitude bound `|a_{ν,j}(f)| ≤ max Cb 0 · ‖f‖_𝓘` from `YoungBounded` on `[0, Sg/ν]`
(source 4480-4490). -/
theorem norm_aFrozen_le_testedNorm {pk : YoungPkg} {lam κ μ : ℂ} {ν Sg Tf Cb : ℝ}
    (hν : 0 < ν) (hTf : Tf ≤ Sg / ν) (j : Bool)
    (hCb : ∀ s ∈ Icc (0 : ℝ) (Sg / ν), ‖pk.ell j s‖ ≤ Cb)
    {f : ℝ → pk.X}
    (hW : Integrable (fun t : ℝ => t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ * ‖f t‖)
      (volume.restrict (Ioc 0 Tf))) :
    ‖aFrozen pk j lam κ ν μ Tf f‖ ≤ max Cb 0 * testedNorm pk lam κ ν μ Tf f := by
  unfold aFrozen testedNorm
  have h1 : ‖∫ t in Ioc 0 Tf, ((t : ℂ) ^ μ) * (Fpm j lam κ ν t 0)⁻¹ * (pk.ell j t) (f t)‖ ≤
      ∫ t in Ioc 0 Tf, ‖((t : ℂ) ^ μ) * (Fpm j lam κ ν t 0)⁻¹ * (pk.ell j t) (f t)‖ :=
    norm_integral_le_integral_norm _
  have h2 : ∫ t in Ioc 0 Tf, ‖((t : ℂ) ^ μ) * (Fpm j lam κ ν t 0)⁻¹ * (pk.ell j t) (f t)‖ ≤
      ∫ t in Ioc 0 Tf, max Cb 0 * (t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ * ‖f t‖) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hW.const_mul (max Cb 0)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htS : t ∈ Icc (0 : ℝ) (Sg / ν) := ⟨ht0, ht.2.trans hTf⟩
    have hmod : ‖Fpm j lam κ ν t 0‖ = ‖Fpm true lam κ ν t 0‖ := by
      cases j
      · exact (fpm_facts ν hν lam κ t 0 ht0 le_rfl).2.2
      · rfl
    have hl : ‖(pk.ell j t) (f t)‖ ≤ max Cb 0 * ‖f t‖ :=
      ((pk.ell j t).le_opNorm (f t)).trans
        (mul_le_mul_of_nonneg_right ((hCb t htS).trans (le_max_left Cb 0)) (norm_nonneg _))
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, hmod]
    have hrp : 0 ≤ t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ :=
      mul_nonneg (Real.rpow_nonneg ht0 _) (inv_nonneg.2 (norm_nonneg _))
    calc t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ * ‖(pk.ell j t) (f t)‖
        ≤ t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ * (max Cb 0 * ‖f t‖) :=
          mul_le_mul_of_nonneg_left hl hrp
      _ = max Cb 0 * (t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ * ‖f t‖) := by ring
  rw [integral_const_mul] at h2
  exact h1.trans h2

/-- Cocycle propagation of the Duhamel integral above the forcing support: for `0 ≤ Tf ≤ H ≤ s`
and `f = 0` on `(Tf, ∞)`, `duhamel pk μ f s = pk.Uev s H (duhamel pk μ f H)` (source 4509-4510). -/
theorem duhamel_cocycle_of_ge {pk : YoungPkg} {conjX : pk.X → pk.X}
    (hL : YoungLaws pk conjX) {μ : ℂ} {Tf H s : ℝ} (hTfH : Tf ≤ H) (hHs : H ≤ s)
    {f : ℝ → pk.X} (hf : ∀ t, Tf < t → f t = 0)
    (hInt : Integrable (fun t : ℝ => ((t : ℂ) ^ μ) • pk.Uev H t (f t))
      (volume.restrict (Ioc 0 H))) :
    duhamel pk μ f s = pk.Uev s H (duhamel pk μ f H) := by
  have hsub : Ioc (0 : ℝ) H ⊆ Ioc 0 s := Ioc_subset_Ioc_right hHs
  have h1 : duhamel pk μ f s = ∫ t in Ioc 0 H, ((t : ℂ) ^ μ) • pk.Uev s t (f t) := by
    unfold duhamel
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub ?_
    intro t ht
    have hlt : Tf < t := lt_of_le_of_lt hTfH (not_le.1 fun hle => ht.2 ⟨ht.1.1, hle⟩)
    rw [hf t hlt, map_zero, smul_zero]
  have h2 : (∫ t in Ioc 0 H, ((t : ℂ) ^ μ) • pk.Uev s t (f t)) =
      ∫ t in Ioc 0 H, pk.Uev s H (((t : ℂ) ^ μ) • pk.Uev H t (f t)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [map_smul, ← ContinuousLinearMap.comp_apply, hL.trans s H t ht.1.le ht.2 hHs]
  rw [h1, h2, ContinuousLinearMap.integral_comp_comm _ hInt]
  rfl

/-- Unforced cocycle evolution of `bareCol`: for `0 ≤ H ≤ s`, `𝒰(s,H)(bareCol S a H) = bareCol S a s`
(source 4509-4510). -/
theorem uev_bareCol {S : FlatSetting} (hL : YoungLaws S.pk S.conjX) (a : ℂ) {H s : ℝ}
    (h0H : 0 ≤ H) (hHs : H ≤ s) :
    S.pk.Uev s H (bareCol S a H) = bareCol S a s := by
  unfold bareCol
  rw [map_add, map_smul, map_smul, ← hL.conj_U, ← ContinuousLinearMap.comp_apply,
    hL.trans s H 0 le_rfl h0H hHs]

/-- `2 / ν ≤ ν^{-3/2}` when `0 < ν ≤ 1 / 4`. -/
theorem two_div_le_uo {ν : ℝ} (hν : 0 < ν) (hν4 : ν ≤ 1 / 4) :
    2 / ν ≤ ν ^ (-(3 / 2 : ℝ)) := by
  have hsq : Real.sqrt ν ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num]
    exact Real.sqrt_le_sqrt hν4
  have hsqpos : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h2 : 2 ≤ (Real.sqrt ν)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsqpos]
    exact hsq.trans_eq (by norm_num)
  have heq : ν ^ (-(3 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ / ν := by
    calc ν ^ (-(3 / 2 : ℝ)) = ν ^ (-(1 / 2 : ℝ) + (-1 : ℝ)) := by congr 1; norm_num
      _ = ν ^ (-(1 / 2 : ℝ)) * ν ^ (-1 : ℝ) := Real.rpow_add hν _ _
      _ = (Real.sqrt ν)⁻¹ / ν := by
        rw [Real.rpow_neg hν.le, Real.sqrt_eq_rpow, Real.rpow_neg_one, ← div_eq_mul_inv]
  rw [heq]
  exact div_le_div_of_nonneg_right h2 hν.le

/-! ## 4. Shared tail reduction for `G1/5/2` (`TailBound`) -/

/-- **`G1.LaterOutput.TailBound` from `LaterOutputAbsOp` and `G1.GBAdmissible`**
(source 4440-4457, 4509-4510): on `s > 2/ν`, `ξ_B(s) = xiFromH (duhamel H) s` by
`duhamel_cocycle_of_ge`. -/
theorem tailBound_of_laterOutputAbsOp (D : SeqData) (hOp : LaterOutputAbsOp D)
    (hGBA : G1.GBAdmissible D) : G1.LaterOutput.TailBound D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨C, N1, _, hC⟩ := hOp dm dp hst κ hκ m hm S hS
  obtain ⟨N2, hA⟩ := hGBA dm dp hst κ hκ m hm S hS
  obtain ⟨N3, hAct⟩ := eventually_atTop.1 hS
  refine ⟨C, max (max N1 N2) N3, fun n hn k hk z hz B hB => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨FI, hFI⟩ := hAct n hn3
  have hL : YoungLaws (S n).pk (S n).conjX := by
    rw [hFI]; exact FlatSettingInst.youngLaws_actualPk FI
  obtain ⟨hf_hi, _, hf_int, -⟩ := hA n hn2 z hz B hB
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hTfH : 1.1 / nu D n ≤ 2 / nu D n := div_le_div_of_nonneg_right (by norm_num) hν.le
  set xH := duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)
  obtain ⟨hint, hbd⟩ := hC n hn1 k hk z hz xH
  have hcongr : EqOn (tailAbsIntegrand (S n) (nu D n) (D.mu n z) k xH)
      (G1.LaterOutput.integrand D S n k z B) (Ioi (2 / nu D n)) := by
    intro s hs
    have hHs : 2 / nu D n ≤ s := le_of_lt hs
    have hxi : xiFromH (S n) (nu D n) (D.mu n z) xH s = (S n).xi (D.mu n z : ℂ) B s := by
      unfold xiFromH FlatSetting.xi xH
      rw [duhamel_cocycle_of_ge hL hTfH hHs hf_hi hf_int]
    unfold tailAbsIntegrand G1.LaterOutput.integrand
    rw [hxi]
  refine ⟨hint.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr]
  exact hbd.trans_eq (by unfold G1.LaterOutput.rhs oldScaleA xH; ring)

/-! ## 5. Proof of `ctAnisoMellin_of` (combining `CTMellin` and `CTAnisotropy`) -/

/-- **Combined canonical Mellin and stress anisotropy** from `IIIa.CTMellin` and
`IIIa.CTAnisotropy` (source 3314-3343, 3392-3401). -/
theorem ctAnisoMellin_of (hM : IIIa.CTMellin) (hA : IIIa.CTAnisotropy) : CTAnisoMellin := by
  intro P hP m hm K hK ε hε
  obtain ⟨Cμ, hCμ0, hCμ⟩ : ∃ Cμ : ℝ, 0 ≤ Cμ ∧ ∀ μ ∈ K, ‖3 * Complex.I * (μ + 3 / 2)‖ ≤ Cμ := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, fun _ h => False.elim h⟩
    · have hcont : ContinuousOn (fun μ : ℂ => ‖3 * Complex.I * (μ + 3 / 2)‖) K :=
        ((continuous_const.mul (continuous_id.add continuous_const)).norm).continuousOn
      obtain ⟨μ₀, hμ₀, hmax⟩ := hK.1.exists_isMaxOn hne hcont
      exact ⟨‖3 * Complex.I * (μ₀ + 3 / 2)‖, norm_nonneg _, fun μ hμ => hmax hμ⟩
  set Dden : ℝ := 1 + Cμ * (Real.pi / 4)
  have hden : 0 < Dden := by positivity
  set δ : ℝ := (ε / 2) / Dden
  have hδ : 0 < δ := div_pos (half_pos hε) hden
  filter_upwards [hM P hP m hm K hK δ hδ, hA P hP m hm K hK δ hδ,
    eventually_nhdsWithin_of_forall (fun ν (hν : ν ∈ Ioi (0 : ℝ)) => hν)] with ν hMν hAν hνpos
  intro tr htr w u hflow μ hμ
  obtain ⟨_, hMb⟩ := hMν tr htr w u hflow μ hμ
  obtain ⟨hAi, hAb⟩ := hAν tr htr w u hflow μ hμ
  refine ⟨hAi, ?_⟩
  have hν : 0 < ν := hνpos
  set S : ℂ := -((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν /
    (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) * (ν : ℂ) ^ (3 + 2 * μ)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcpos : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hSnorm : ‖S‖ = (Real.pi / 4) * IIIa.scaleA P ν μ := by
    unfold S IIIa.scaleA
    have hpow : ‖(ν : ℂ) ^ (3 + 2 * μ)‖ = ν ^ (3 + 2 * μ.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hν]
      simp
    rw [norm_mul, norm_div, norm_mul, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hpi.le, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hcpos.le, hpow]
    ring
  have hSne : S ≠ 0 := by
    unfold S
    have h1 : -((Real.pi : ℝ) : ℂ) ≠ 0 := neg_ne_zero.2 (Complex.ofReal_ne_zero.2 hpi.ne')
    have h2 : P.gaugeFactor ν ≠ 0 := by
      unfold UnforcedLeray.Blueprint.Planar.PlanarData.gaugeFactor
      exact mul_ne_zero (Complex.exp_ne_zero _)
        (by rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hν.ne')]; exact Complex.exp_ne_zero _)
    have h3 : (4 : ℂ) * ((ν ^ (-2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 hcpos.ne')
    have h4 : (ν : ℂ) ^ (3 + 2 * μ) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hν.ne')]
      exact Complex.exp_ne_zero _
    exact mul_ne_zero (div_ne_zero (mul_ne_zero h1 h2) h3) h4
  have hiA : ‖IIIa.iA ν μ w - S * IIIa.mellinJc P μ‖ ≤
      (Real.pi / 4) * δ * IIIa.scaleA P ν μ := by
    have heq : IIIa.iA ν μ w - S * IIIa.mellinJc P μ =
        S * (IIIa.iA ν μ w / S - IIIa.mellinJc P μ) := by
      rw [mul_sub, mul_div_cancel₀ _ hSne]
    rw [heq, norm_mul, hSnorm]
    have hsc0 : 0 ≤ (Real.pi / 4) * IIIa.scaleA P ν μ := by
      rw [← hSnorm]; exact norm_nonneg S
    calc (Real.pi / 4) * IIIa.scaleA P ν μ * ‖IIIa.iA ν μ w / S - IIIa.mellinJc P μ‖
        ≤ (Real.pi / 4) * IIIa.scaleA P ν μ * δ := mul_le_mul_of_nonneg_left hMb hsc0
      _ = (Real.pi / 4) * δ * IIIa.scaleA P ν μ := by ring
  have hsc0 : 0 ≤ IIIa.scaleA P ν μ := by
    unfold IIIa.scaleA
    exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)) hcpos.le
  set I := ∫ s in Ioi (IIIa.onsetAge ν), (2 * IIIa.pairQ tr μ (u s) s -
    IIIa.pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)
  set M := 3 * Complex.I * (μ + 3 / 2)
  have htri : ‖I - M * S * IIIa.mellinJc P μ‖ ≤
      ‖I - M * IIIa.iA ν μ w‖ + ‖M‖ * ‖IIIa.iA ν μ w - S * IIIa.mellinJc P μ‖ := by
    have heq : I - M * S * IIIa.mellinJc P μ =
        (I - M * IIIa.iA ν μ w) + M * (IIIa.iA ν μ w - S * IIIa.mellinJc P μ) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans (by rw [norm_mul])
  have hMle : ‖M‖ * ‖IIIa.iA ν μ w - S * IIIa.mellinJc P μ‖ ≤
      Cμ * ((Real.pi / 4) * δ * IIIa.scaleA P ν μ) :=
    mul_le_mul (hCμ μ hμ) hiA (norm_nonneg _) hCμ0
  calc ‖I - M * S * IIIa.mellinJc P μ‖
      ≤ δ * IIIa.scaleA P ν μ + Cμ * ((Real.pi / 4) * δ * IIIa.scaleA P ν μ) :=
        htri.trans (add_le_add hAb hMle)
    _ = (Dden * δ) * IIIa.scaleA P ν μ := by
        unfold Dden; ring
    _ = (ε / 2) * IIIa.scaleA P ν μ := by
        dsimp only [δ]
        rw [mul_div_cancel₀ _ hden.ne']
    _ ≤ ε * IIIa.scaleA P ν μ :=
        mul_le_mul_of_nonneg_right (by linarith) hsc0

/-! ## 6. Proof of `bareColAniso_of_unit` and `oldAnisoTested_of` -/

/-- Decomposition of `xiBare S μ a s` into real and imaginary unit bare columns. -/
theorem xiBare_eq_re_im (S : FlatSetting) (μ : ℝ) (a : ℂ) (s : ℝ) :
    xiBare S μ a s =
      (a.re : ℂ) • xiBare S μ 1 s + (a.im : ℂ) • xiBare S μ Complex.I s := by
  unfold xiBare bareCol
  have ha : (a.re : ℂ) * (1 : ℂ) + (a.im : ℂ) * Complex.I = a := by
    apply Complex.ext <;> simp
  have hac : (a.re : ℂ) * (starRingEnd ℂ (1 : ℂ)) +
      (a.im : ℂ) * (starRingEnd ℂ Complex.I) = starRingEnd ℂ a := by
    apply Complex.ext <;> simp
  rw [smul_comm (a.re : ℂ), smul_comm (a.im : ℂ), ← smul_add]
  congr 1
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
    add_add_add_comm, ← add_smul, ← add_smul, ha, hac]

/-- Decomposition of `bareColLead D S n z a` into real and imaginary unit parts. -/
theorem bareColLead_eq_re_im (D : SeqData) (S : FlatSetting) (n : ℕ) (z : ℝ) (a : ℂ) :
    bareColLead D S n z a =
      a.re * bareColLead D S n z 1 + a.im * bareColLead D S n z Complex.I := by
  unfold bareColLead
  have him : (a * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).im =
      a.re * (1 * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)).im +
      a.im * (Complex.I * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) *
        planarJ D.Pl (D.mu n z : ℂ)).im := by
    rw [mul_assoc a, mul_assoc 1, mul_assoc Complex.I]
    simp [Complex.mul_im]
  rw [him]
  ring

/-- Extraction of a null sequence `ω_can : ℕ → ℝ` from a uniform-in-window `∀ ε > 0` bound. -/
private theorem omega_of_forall_eps {f g : ℕ → ℝ → ℝ}
    (hf0 : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, 0 ≤ f n z)
    (hg0 : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, 0 < g n z)
    (hlim : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, f n z ≤ ε * g n z) :
    ∃ (ωcan : ℕ → ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧ (∀ n, 0 ≤ ωcan n) ∧
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, f n z ≤ ωcan n * g n z := by
  classical
  set A : ℕ → Set ℝ := fun n => (fun z => f n z / g n z) '' Icc (-1 : ℝ) 1
  set ωcan : ℕ → ℝ := fun n => if BddAbove (A n) then sSup (A n) else 0
  have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hω0 : ∀ n, 0 ≤ ωcan n := by
    intro n
    dsimp only [ωcan]
    split_ifs with hB
    · have h0 : 0 ≤ f n 0 / g n 0 := div_nonneg (hf0 n 0 h0mem) (hg0 n 0 h0mem).le
      exact h0.trans (le_csSup hB ⟨0, h0mem, rfl⟩)
    · exact le_rfl
  have hbnd : ∀ {ε : ℝ}, 0 < ε → ∀ {n : ℕ},
      (∀ z ∈ Icc (-1 : ℝ) 1, f n z ≤ ε * g n z) →
      BddAbove (A n) ∧ ωcan n ≤ ε := by
    intro ε _ n hn
    have hB : BddAbove (A n) := by
      refine ⟨ε, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact (div_le_iff₀ (hg0 n z hz)).2 (hn z hz)
    refine ⟨hB, ?_⟩
    dsimp only [ωcan]
    rw [ite_eq_left_iff.2 fun h => (h hB).elim]
    refine csSup_le ⟨f n 0 / g n 0, 0, h0mem, rfl⟩ ?_
    rintro y ⟨z, hz, rfl⟩
    exact (div_le_iff₀ (hg0 n z hz)).2 (hn z hz)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim 1 one_pos)
  refine ⟨ωcan, N, ?_, hω0, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Nε, hNε⟩ := eventually_atTop.1 (hlim (ε / 2) (half_pos hε))
    refine ⟨Nε, fun n hn => ?_⟩
    have hle := (hbnd (half_pos hε) (hNε n hn)).2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hω0 n)]
    linarith
  · intro n hn z hz
    have hB := (hbnd one_pos (hN n hn)).1
    have hle : f n z / g n z ≤ ωcan n := by
      dsimp only [ωcan]
      rw [ite_eq_left_iff.2 fun h => (h hB).elim]
      exact le_csSup hB ⟨z, hz, rfl⟩
    exact (div_le_iff₀ (hg0 n z hz)).1 hle

/-- **`BareColAniso` from `OldReadoutLinear` and `BareColUnit`** (source 4520-4543). -/
theorem bareColAniso_of_unit (D : SeqData) (hLin : OldReadoutLinear D) (hU : BareColUnit D) :
    BareColAniso D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨Nlin, hNlin⟩ := hLin dm dp hst κ hκ m hm S hS
  obtain ⟨⟨Nint, hNint⟩, hUlim⟩ := hU dm dp hst κ hκ m hm S hS
  have hevc : ∀ᶠ n : ℕ in atTop, (S n).c = cOf (nu D n) := by
    filter_upwards [hS] with n hn
    obtain ⟨FI, hFI⟩ := hn
    rw [hFI]; rfl
  obtain ⟨Nc, hNc⟩ := eventually_atTop.1 hevc
  set f : ℕ → ℝ → ℝ := fun n z =>
    |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) - bareColLead D (S n) n z 1| +
    |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
      bareColLead D (S n) n z Complex.I|
  set g : ℕ → ℝ → ℝ := fun n z =>
    ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
      cOf (nu D n)
  have hf0 : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, 0 ≤ f n z :=
    fun n z _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg0 : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, 0 < g n z := by
    intro n z _
    unfold g
    have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
    have hNpos : 0 < ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ := by
      unfold Nnu
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hν]
      exact mul_pos (Complex.norm_exp _ ▸ Real.exp_pos _) (Real.rpow_pos_of_pos hν _)
    exact div_pos (mul_pos hNpos (Real.rpow_pos_of_pos hν _)) (cOf_pos hν)
  have hlim : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, f n z ≤ ε * g n z := by
    intro ε hε
    filter_upwards [hUlim (ε / 2) (half_pos hε), eventually_ge_atTop Nc] with n hn hnc z hz
    obtain ⟨h1, h2⟩ := hn z hz
    have hceq : oldScaleA D (S n) n z = g n z := by
      unfold oldScaleA g
      rw [hNc n hnc]
    rw [hceq] at h1 h2
    unfold f
    linarith
  obtain ⟨ωcan, Nω, hωtend, hω0, hωle⟩ := omega_of_forall_eps hf0 hg0 hlim
  refine ⟨ωcan, 1, max (max Nlin Nint) (max Nc Nω), hωtend, hω0, zero_le_one,
    fun n hn z hz a => ?_⟩
  have hnlin : Nlin ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnint : Nint ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnc : Nc ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnω : Nω ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hi1, hiI⟩ := hNint n hnint z hz
  have hdens : ∀ s : ℝ,
      itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) a) s =
        a.re * itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) s +
        a.im * itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) s := by
    intro s
    unfold itOldDens FlatSetting.ITdens
    by_cases hs : nu D n ^ (-(3 / 2 : ℝ)) ≤ s
    · simp only [ite_eq_left_iff.2 fun h => (h hs).elim]
      rw [xiBare_eq_re_im (S n) (D.mu n z) a s,
        (hNlin n hnlin s _ _ 0).1,
        (hNlin n hnlin s (xiBare (S n) (D.mu n z) 1 s) 0 a.re).2,
        (hNlin n hnlin s (xiBare (S n) (D.mu n z) Complex.I s) 0 a.im).2]
      ring
    · simp only [ite_eq_right_iff.2 fun h => (hs h).elim, cellInt, Matrix.zero_apply,
        mul_zero, sub_self, integral_zero, add_zero]
  have hint_a : Integrable (itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) a))
      (volume.restrict (Ioi (0 : ℝ))) := by
    rw [funext hdens]
    exact (hi1.const_mul a.re).add (hiI.const_mul a.im)
  have hit_a : itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) a) =
      a.re * itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) +
      a.im * itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) := by
    change (∫ s in Ioi (0 : ℝ), itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) a) s) = _
    rw [funext hdens, integral_add (hi1.const_mul a.re) (hiI.const_mul a.im),
      integral_const_mul, integral_const_mul]
    rfl
  refine ⟨hint_a, ?_⟩
  rw [hit_a, bareColLead_eq_re_im]
  have hsub : a.re * itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) +
        a.im * itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
        (a.re * bareColLead D (S n) n z 1 + a.im * bareColLead D (S n) n z Complex.I) =
      a.re * (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) - bareColLead D (S n) n z 1) +
      a.im * (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
        bareColLead D (S n) n z Complex.I) := by ring
  rw [hsub]
  have h1 := abs_add_le
    (a.re * (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) - bareColLead D (S n) n z 1))
    (a.im * (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
      bareColLead D (S n) n z Complex.I))
  rw [abs_mul, abs_mul] at h1
  have hre : |a.re| ≤ ‖a‖ := Complex.abs_re_le_norm a
  have him : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
  have h2 : |a.re| * |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) - bareColLead D (S n) n z 1| +
      |a.im| * |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
        bareColLead D (S n) n z Complex.I| ≤ ‖a‖ * f n z := by
    unfold f
    nlinarith [abs_nonneg (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) -
        bareColLead D (S n) n z 1),
      abs_nonneg (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
        bareColLead D (S n) n z Complex.I)]
  have hceq : oldScaleA D (S n) n z = g n z := by
    unfold oldScaleA g
    rw [hNc n hnc]
  calc |a.re * (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) 1) - bareColLead D (S n) n z 1) +
        a.im * (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) Complex.I) -
           bareColLead D (S n) n z Complex.I)|
      ≤ ‖a‖ * f n z := h1.trans h2
    _ ≤ ‖a‖ * (ωcan n * g n z) := mul_le_mul_of_nonneg_left (hωle n hnω z hz) (norm_nonneg a)
    _ = 1 * (oldScaleA D (S n) n z * ωcan n) * ‖a‖ := by rw [hceq]; ring

/-- **Conditional assembly of `OldAnisoTested D`** (source 4501-4543, 4665-4676):
from `DuhamelDecomp`, `OldReadoutLinear`, `LaterOutputRem`, and `BareColUnit`.
Composed by task `PartIII-b:IIIb-D3/2/G3/1` (`OldAniso.lean`). -/
theorem oldAnisoTested_of (D : SeqData) (hDuh : DuhamelDecomp D) (hLin : OldReadoutLinear D)
    (hRem : LaterOutputRem D) (hU : BareColUnit D) : OldAnisoTested D := by
  have hBare := bareColAniso_of_unit D hLin hU
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨Cduh, Camp, Nduh, hCduh0, hCamp0, hNduh⟩ := hDuh dm dp hst κ hκ m hm S hS
  obtain ⟨Nlin, hNlin⟩ := hLin dm dp hst κ hκ m hm S hS
  obtain ⟨Crem, Nrem, hCrem0, hNrem⟩ := hRem dm dp hst κ hκ m hm S hS
  obtain ⟨ωcan, Cbare, Nbare, hωtend, hω0, hCbare0, hNbare⟩ := hBare dm dp hst κ hκ m hm S hS
  have hev : ∀ᶠ n : ℕ in atTop, (S n).c = cOf (nu D n) ∧ nu D n < 1 / 4 := by
    refine ( ?_ : ∀ᶠ n : ℕ in atTop, (S n).c = cOf (nu D n)).and
      ((retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
    filter_upwards [hS] with n hn
    obtain ⟨FI, hFI⟩ := hn
    rw [hFI]; rfl
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set C := Cbare * Camp + Crem * Cduh
  have hC0 : 0 ≤ C := by positivity
  refine ⟨ωcan, C, max (max (max Nduh Nlin) (max Nrem Nbare)) N0, hωtend, hω0, hC0,
    fun n hn z hz B hB => ?_⟩
  have hnduh : Nduh ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hn)
  have hnlin : Nlin ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hn)
  have hnrem : Nrem ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hn)
  have hnbare : Nbare ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hn)
  have hn0 : N0 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hc, hν4⟩ := hN0 n hn0
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have huo : 2 / nu D n ≤ nu D n ^ (-(3 / 2 : ℝ)) := two_div_le_uo hν hν4.le
  obtain ⟨hxi_eq, hrH_bd, ha_bd⟩ := hNduh n hnduh z hz B hB
  set aPlus := (S n).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu n z : ℂ) (nu D n) B
  set rH := duhRemH D (S n) n z B
  set tN := testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ)
    (1.1 / nu D n) ((S n).gB B)
  have htN0 : 0 ≤ tN := by
    unfold tN testedNorm
    exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
        (norm_nonneg _)
  obtain ⟨hint_bare, hbd_bare⟩ := hNbare n hnbare z hz aPlus
  obtain ⟨hint_rem, hbd_rem⟩ := hNrem n hnrem z hz rH
  have hdens_split : ∀ s : ℝ,
      itOldDens (S n) (nu D n) ((S n).xi (D.mu n z : ℂ) B) s =
        itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) s +
        itOldDens (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH) s := by
    intro s
    unfold itOldDens FlatSetting.ITdens
    by_cases hs : nu D n ^ (-(3 / 2 : ℝ)) ≤ s
    · simp only [ite_eq_left_iff.2 fun h => (h hs).elim]
      rw [hxi_eq s (le_trans huo hs), (hNlin n hnlin s _ _ 0).1]
      ring
    · simp only [ite_eq_right_iff.2 fun h => (hs h).elim, cellInt, Matrix.zero_apply,
        mul_zero, sub_self, integral_zero, add_zero]
  have hit_split : itOld (S n) (nu D n) ((S n).xi (D.mu n z : ℂ) B) =
      itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) +
      itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH) := by
    change (∫ s in Ioi (0 : ℝ), itOldDens (S n) (nu D n) ((S n).xi (D.mu n z : ℂ) B) s) = _
    rw [funext hdens_split, integral_add hint_bare hint_rem]
    rfl
  change |itOld (S n) (nu D n) ((S n).xi (D.mu n z : ℂ) B) - bareColLead D (S n) n z aPlus| ≤
    C * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN
  have hA0 : 0 ≤ oldScaleA D (S n) n z := by
    unfold oldScaleA
    rw [hc]
    exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)) (cOf_pos hν).le
  have hFne : ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((fpm_facts (nu D n) hν D.Pl.eigenvalue D.Pl.kappa (2 / nu D n) 0
      (by positivity) le_rfl).2.1 true)
  have h1 : |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) -
        bareColLead D (S n) n z aPlus| ≤
      Cbare * Camp * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN := by
    have h1a : Cbare * (oldScaleA D (S n) n z * ωcan n) * ‖aPlus‖ ≤
        Cbare * (oldScaleA D (S n) n z * ωcan n) * (Camp * tN) :=
      mul_le_mul_of_nonneg_left ha_bd (mul_nonneg hCbare0 (mul_nonneg hA0 (hω0 n)))
    have h1b : Cbare * (oldScaleA D (S n) n z * ωcan n) * (Camp * tN) ≤
        Cbare * Camp * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN := by
      have : 0 ≤ Cbare * Camp * oldScaleA D (S n) n z * tN * nu D n := by positivity
      linarith
    exact hbd_bare.trans (h1a.trans h1b)
  have h2 : |itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH)| ≤
      Crem * Cduh * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN := by
    have h2a : Crem * oldScaleA D (S n) n z *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖rH‖) ≤
        Crem * oldScaleA D (S n) n z *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
            (Cduh * nu D n * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ * tN)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrH_bd (inv_nonneg.2 (norm_nonneg _)))
        (mul_nonneg hCrem0 hA0)
    have h2b : Crem * oldScaleA D (S n) n z *
          (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
            (Cduh * nu D n * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ * tN)) =
        Crem * Cduh * (oldScaleA D (S n) n z * nu D n) * tN := by
      calc Crem * oldScaleA D (S n) n z *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
              (Cduh * nu D n * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖ * tN))
          = Crem * Cduh * (oldScaleA D (S n) n z * nu D n) * tN *
              (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
                ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖) := by ring
        _ = Crem * Cduh * (oldScaleA D (S n) n z * nu D n) * tN := by
            rw [inv_mul_cancel₀ hFne, mul_one]
    have h2c : Crem * Cduh * (oldScaleA D (S n) n z * nu D n) * tN ≤
        Crem * Cduh * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN := by
      have hωn0 : 0 ≤ ωcan n := hω0 n
      have : 0 ≤ Crem * Cduh * oldScaleA D (S n) n z * tN * ωcan n := by positivity
      linarith
    exact hbd_rem.trans ((h2a.trans_eq h2b).trans h2c)
  rw [hit_split]
  have htri : |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) +
        itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH) -
        bareColLead D (S n) n z aPlus| ≤
      |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) - bareColLead D (S n) n z aPlus| +
      |itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH)| := by
    have heq : itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) +
        itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH) -
        bareColLead D (S n) n z aPlus =
      (itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) - bareColLead D (S n) n z aPlus) +
        itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH) := by ring
    rw [heq]
    exact abs_add_le _ _
  calc |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) aPlus) +
        itOld (S n) (nu D n) (xiFromH (S n) (nu D n) (D.mu n z) rH) -
        bareColLead D (S n) n z aPlus|
      ≤ Cbare * Camp * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN +
        Crem * Cduh * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN :=
        htri.trans (add_le_add h1 h2)
    _ = C * (oldScaleA D (S n) n z * (nu D n + ωcan n)) * tN := by
        unfold C; ring

end G3

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

end
