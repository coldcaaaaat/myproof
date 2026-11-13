import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Fin

open Matrix Equiv
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-! ### 0. 基础分支归约与有限集对合重排辅助引理 -/

lemma ite_pos_eq {α : Sort*} {P : Prop} [inst : Decidable P] (h : P) (a b : α) :
    (if P then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd h hnp

lemma ite_neg_eq {α : Sort*} {P : Prop} [inst : Decidable P] (h : ¬P) (a b : α) :
    (if P then a else b) = b := by
  cases inst with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

lemma dite_pos_eq {α : Sort*} {P : Prop} [inst : Decidable P] (h : P) (a : P → α) (b : ¬P → α) :
    (if hp : P then a hp else b hp) = a h := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd h hnp

lemma dite_neg_eq {α : Sort*} {P : Prop} [inst : Decidable P] (h : ¬P) (a : P → α) (b : ¬P → α) :
    (if hp : P then a hp else b hp) = b h := by
  cases inst with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-- 按谓词 `p` 拆分有限集求和 -/
lemma sum_split_filter {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    (∑ x ∈ s, f x) =
    (∑ x ∈ s.filter p, f x) + (∑ x ∈ s.filter (fun x => ¬p x), f x) := by
  exact (Finset.sum_filter_add_sum_filter_not s p f).symm

/-- 利用全局对合 `φ` 重排两个有限子集上的求和 -/
lemma sum_reindex_involutive {α β : Type*} [AddCommMonoid β]
    (s t : Finset α) (φ : α → α) (f : α → β)
    (h_inv : ∀ x, φ (φ x) = x)
    (hst : ∀ x ∈ s, φ x ∈ t)
    (hts : ∀ y ∈ t, φ y ∈ s) :
    (∑ y ∈ t, f y) = (∑ x ∈ s, f (φ x)) := by
  classical
  have ht_eq : t = s.image φ := by
    ext y
    rw [Finset.mem_image]
    constructor
    · intro hy
      exact ⟨φ y, hts y hy, h_inv y⟩
    · rintro ⟨x, hx, rfl⟩
      exact hst x hx
  rw [ht_eq, Finset.sum_image]
  intro x₁ _ x₂ _ h_eq
  have := congrArg φ h_eq
  rwa [h_inv x₁, h_inv x₂] at this

/-- 双射下的全集求和转换引理 -/
lemma sum_univ_equiv {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ]
    (e : α ≃ β) (f : α → γ) (g : β → γ) (hfg : ∀ a, f a = g (e a)) :
    (∑ a : α, f a) = (∑ b : β, g b) := by
  classical
  have h1 : (∑ a : α, f a) = (∑ a : α, g (e a)) :=
    Finset.sum_congr rfl (fun a _ => hfg a)
  have h_univ : (Finset.univ : Finset β) = (Finset.univ : Finset α).image e := by
    ext b
    rw [Finset.mem_image]
    constructor
    · intro _
      exact ⟨e.symm b, Finset.mem_univ _, e.apply_symm_apply b⟩
    · intro _
      exact Finset.mem_univ b
  have h2 : (∑ b : β, g b) = (∑ a : α, g (e a)) := by
    rw [h_univ, Finset.sum_image]
    intro a₁ _ a₂ _ h_eq
    exact e.injective h_eq
  exact h1.trans h2.symm

/-! ### 1. 0-1 格路、后缀交换算子 `swapSuffix` 与首交点谓词 -/

/-- 在时刻 `t₀` 之后交换第 `i₀` 条与第 `j₀` 条格路的后缀 -/
def swapSuffix {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m) (k : Fin m) (t : Fin (N + 1)) : ℤ :=
  if t ≤ t₀ then u k t else u (Equiv.swap i₀ j₀ k) t

@[simp]
lemma swapSuffix_le {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ k : Fin m) {t : Fin (N + 1)} (ht : t ≤ t₀) :
    swapSuffix u t₀ i₀ j₀ k t = u k t := by
  unfold swapSuffix
  exact ite_pos_eq ht _ _

@[simp]
lemma swapSuffix_gt {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ k : Fin m) {t : Fin (N + 1)} (ht : ¬(t ≤ t₀)) :
    swapSuffix u t₀ i₀ j₀ k t = u (Equiv.swap i₀ j₀ k) t := by
  unfold swapSuffix
  exact ite_neg_eq ht _ _

/-- `swapSuffix` 对任意固定的 `(t₀, i₀, j₀)` 严格是对合 -/
@[simp]
lemma swapSuffix_involutive {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m) :
    swapSuffix (swapSuffix u t₀ i₀ j₀) t₀ i₀ j₀ = u := by
  funext k t
  by_cases ht : t ≤ t₀
  · rw [swapSuffix_le _ _ _ _ _ ht, swapSuffix_le _ _ _ _ _ ht]
  · rw [swapSuffix_gt _ _ _ _ _ ht, swapSuffix_gt _ _ _ _ _ ht, Equiv.swap_apply_self]

/-- 当 `u i₀ t₀ = u j₀ t₀` 时，在时刻 `t₀` 处用 `swap i₀ j₀` 置换下标不改变格点位置 -/
lemma swap_eq_at_t₀ {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m) (h_eq : u i₀ t₀ = u j₀ t₀) (k : Fin m) :
    u (Equiv.swap i₀ j₀ k) t₀ = u k t₀ := by
  rcases eq_or_ne k i₀ with rfl | hki
  · rw [Equiv.swap_apply_left, h_eq]
  · rcases eq_or_ne k j₀ with rfl | hkj
    · rw [Equiv.swap_apply_right, h_eq]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- **核心引理**：当 `u i₀ t₀ = u j₀ t₀` 时，`swapSuffix` 在分界点 `t₀` 处无缝拼接 -/
lemma step_swapSuffix {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m) (h_eq : u i₀ t₀ = u j₀ t₀)
    (k : Fin m) (t : Fin N) :
    swapSuffix u t₀ i₀ j₀ k t.succ - swapSuffix u t₀ i₀ j₀ k t.castSucc =
    if t.succ ≤ t₀ then
      u k t.succ - u k t.castSucc
    else
      u (Equiv.swap i₀ j₀ k) t.succ - u (Equiv.swap i₀ j₀ k) t.castSucc := by
  by_cases h1 : t.succ ≤ t₀
  · have h2 : t.castSucc ≤ t₀ := by
      change t.val ≤ t₀.val
      change t.val + 1 ≤ t₀.val at h1
      omega
    rw [ite_pos_eq h1, swapSuffix_le _ _ _ _ _ h1, swapSuffix_le _ _ _ _ _ h2]
  · rw [ite_neg_eq h1, swapSuffix_gt _ _ _ _ _ h1]
    by_cases h2 : t.castSucc ≤ t₀
    · have ht_eq : t.castSucc = t₀ := by
        apply Fin.ext
        change t.val = t₀.val
        change t.val ≤ t₀.val at h2
        change ¬(t.val + 1 ≤ t₀.val) at h1
        omega
      rw [swapSuffix_le _ _ _ _ _ h2, ht_eq, swap_eq_at_t₀ u t₀ i₀ j₀ h_eq k]
    · rw [swapSuffix_gt _ _ _ _ _ h2]

/-- 单步权重：增量为 1 时权重为 `x t`，否则为 `1` -/
def stepWt {N : ℕ} (x : Fin N → R) (t : Fin N) (d : ℤ) : R :=
  if d = 1 then x t else 1

/-- 格路簇的总单项式权重 -/
def pathFamilyWt {m N : ℕ} (x : Fin N → R) (u : Fin m → Fin (N + 1) → ℤ) : R :=
  ∏ t : Fin N, ∏ k : Fin m, stepWt x t (u k t.succ - u k t.castSucc)

/-- **定理：后缀交换算子严格保持格路簇的总权重不变** -/
theorem pathFamilyWt_swapSuffix {m N : ℕ} (x : Fin N → R)
    (u : Fin m → Fin (N + 1) → ℤ) (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m)
    (h_eq : u i₀ t₀ = u j₀ t₀) :
    pathFamilyWt x (swapSuffix u t₀ i₀ j₀) = pathFamilyWt x u := by
  unfold pathFamilyWt
  refine Finset.prod_congr rfl (fun t _ => ?_)
  by_cases h1 : t.succ ≤ t₀
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [step_swapSuffix u t₀ i₀ j₀ h_eq k t, ite_pos_eq h1]
  · have h_step : ∀ k,
        stepWt x t (swapSuffix u t₀ i₀ j₀ k t.succ - swapSuffix u t₀ i₀ j₀ k t.castSucc) =
        stepWt x t (u (Equiv.swap i₀ j₀ k) t.succ - u (Equiv.swap i₀ j₀ k) t.castSucc) := by
      intro k
      rw [step_swapSuffix u t₀ i₀ j₀ h_eq k t, ite_neg_eq h1]
    simp_rw [h_step]
    exact Equiv.prod_comp (Equiv.swap i₀ j₀)
      (fun k => stepWt x t (u k t.succ - u k t.castSucc))

/-! ### 2. 首交点三元组 `(t₀, i₀, j₀)` 的唯一性与后缀交换不变性 -/

/-- `(t₀, i₀, j₀)` 是格路簇 `u` 按字典序的第一个相交三元组 -/
structure IsFirstIntersection {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m) : Prop where
  lt_idx : i₀ < j₀
  eq_at : u i₀ t₀ = u j₀ t₀
  min_t : ∀ t < t₀, ∀ i j : Fin m, i < j → u i t ≠ u j t
  min_i : ∀ i < i₀, ∀ j : Fin m, i < j → u i t₀ ≠ u j t₀
  min_j : ∀ j < j₀, i₀ < j → u i₀ t₀ ≠ u j t₀

/-- **引理：首交点三元组 `(t₀, i₀, j₀)` 唯一** -/
theorem IsFirstIntersection.unique {m N : ℕ} {u : Fin m → Fin (N + 1) → ℤ}
    {t₀ t₁ : Fin (N + 1)} {i₀ j₀ i₁ j₁ : Fin m}
    (h0 : IsFirstIntersection u t₀ i₀ j₀) (h1 : IsFirstIntersection u t₁ i₁ j₁) :
    t₀ = t₁ ∧ i₀ = i₁ ∧ j₀ = j₁ := by
  have ht : t₀ = t₁ := by
    rcases lt_trichotomy t₀ t₁ with hlt | rfl | hgt
    · exact absurd h0.eq_at (h1.min_t t₀ hlt i₀ j₀ h0.lt_idx)
    · rfl
    · exact absurd h1.eq_at (h0.min_t t₁ hgt i₁ j₁ h1.lt_idx)
  subst ht
  have hi : i₀ = i₁ := by
    rcases lt_trichotomy i₀ i₁ with hlt | rfl | hgt
    · exact absurd h0.eq_at (h1.min_i i₀ hlt j₀ h0.lt_idx)
    · rfl
    · exact absurd h1.eq_at (h0.min_i i₁ hgt j₁ h1.lt_idx)
  subst hi
  have hj : j₀ = j₁ := by
    rcases lt_trichotomy j₀ j₁ with hlt | rfl | hgt
    · exact absurd h0.eq_at (h1.min_j j₀ hlt h0.lt_idx)
    · rfl
    · exact absurd h1.eq_at (h0.min_j j₁ hgt h1.lt_idx)
  exact ⟨rfl, rfl, hj⟩

/-- **核心引理：`swapSuffix` 保持首交点三元组 `(t₀, i₀, j₀)` 完全不变** -/
theorem IsFirstIntersection.swapSuffix_iff {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (t₀ : Fin (N + 1)) (i₀ j₀ : Fin m) :
    IsFirstIntersection (swapSuffix u t₀ i₀ j₀) t₀ i₀ j₀ ↔
    IsFirstIntersection u t₀ i₀ j₀ := by
  constructor <;> intro h <;> refine ⟨h.lt_idx, ?_, ?_, ?_, ?_⟩
  · have h_eq := h.eq_at
    rw [swapSuffix_le _ _ _ _ _ (le_refl t₀), swapSuffix_le _ _ _ _ _ (le_refl t₀)] at h_eq
    exact h_eq
  · intro t ht i j hij
    have hle : t ≤ t₀ := le_of_lt ht
    have h_ne := h.min_t t ht i j hij
    rw [swapSuffix_le _ _ _ _ _ hle, swapSuffix_le _ _ _ _ _ hle] at h_ne
    exact h_ne
  · intro i hi j hij
    have h_ne := h.min_i i hi j hij
    rw [swapSuffix_le _ _ _ _ _ (le_refl t₀), swapSuffix_le _ _ _ _ _ (le_refl t₀)] at h_ne
    exact h_ne
  · intro j hj hij
    have h_ne := h.min_j j hj hij
    rw [swapSuffix_le _ _ _ _ _ (le_refl t₀), swapSuffix_le _ _ _ _ _ (le_refl t₀)] at h_ne
    exact h_ne
  · rw [swapSuffix_le _ _ _ _ _ (le_refl t₀), swapSuffix_le _ _ _ _ _ (le_refl t₀)]
    exact h.eq_at
  · intro t ht i j hij
    have hle : t ≤ t₀ := le_of_lt ht
    rw [swapSuffix_le _ _ _ _ _ hle, swapSuffix_le _ _ _ _ _ hle]
    exact h.min_t t ht i j hij
  · intro i hi j hij
    rw [swapSuffix_le _ _ _ _ _ (le_refl t₀), swapSuffix_le _ _ _ _ _ (le_refl t₀)]
    exact h.min_i i hi j hij
  · intro j hj hij
    rw [swapSuffix_le _ _ _ _ _ (le_refl t₀), swapSuffix_le _ _ _ _ _ (le_refl t₀)]
    exact h.min_j j hj hij

/-! ### 3. 离散介值定理：斜分拆下不相交 0-1 格路簇必对应恒等置换 `σ = 1` -/

/-- **0-1 格路离散介值引理**：若 `p 0 > q 0` 且每步增量为 0 或 1，且 `p, q` 从不相交，
    则对一切时刻 `t` 恒有 `p t > q t`。 -/
theorem nonIntersecting_gt_of_start_gt {N : ℕ} (p q : Fin (N + 1) → ℤ)
    (h0 : q 0 < p 0)
    (hp : ∀ t : Fin N, p t.succ - p t.castSucc = 0 ∨ p t.succ - p t.castSucc = 1)
    (hq : ∀ t : Fin N, q t.succ - q t.castSucc = 0 ∨ q t.succ - q t.castSucc = 1)
    (h_disj : ∀ t : Fin (N + 1), p t ≠ q t) :
    ∀ t : Fin (N + 1), q t < p t := by
  intro t
  induction t using Fin.induction with
  | zero => exact h0
  | succ t ih =>
    change q t.castSucc < p t.castSucc at ih
    have h_ne : p t.succ ≠ q t.succ := h_disj t.succ
    rcases hp t with hp0 | hp1 <;> rcases hq t with hq0 | hq1 <;> omega

/-- 对任意单调不增的共轭分拆 `μ`，函数 `r ↦ μ r - r` 严格递减 -/
lemma strictAnti_conjShift {m : ℕ} (μ : Fin m → ℕ) (hμ : Antitone μ) :
    StrictAnti (fun r : Fin m => (μ r : ℤ) - (r.val : ℤ)) := by
  intro a b hab
  change (μ b : ℤ) - (b.val : ℤ) < (μ a : ℤ) - (a.val : ℤ)
  have hle : μ b ≤ μ a := hμ (le_of_lt hab)
  have hlt : a.val < b.val := hab
  omega

/-- `Fin m` 上严格递增函数满足 `n ≤ (f ⟨n, hn⟩).val` -/
lemma fin_val_le_of_strictMono {m : ℕ} (f : Fin m → Fin m) (hf : StrictMono f) :
    ∀ (n : ℕ) (hn : n < m), n ≤ (f ⟨n, hn⟩).val := by
  intro n
  induction n with
  | zero =>
    intro _
    exact Nat.zero_le _
  | succ n ih =>
    intro hn
    have hn' : n < m := by omega
    have h_ih : n ≤ (f ⟨n, hn'⟩).val := ih hn'
    have h_lt : (⟨n, hn'⟩ : Fin m) < ⟨n + 1, hn⟩ := by
      change n < n + 1
      omega
    have hf_lt : (f ⟨n, hn'⟩).val < (f ⟨n + 1, hn⟩).val := hf h_lt
    omega

/-- `Fin m` 上的严格保序置换必为恒等置换 `Equiv.refl` -/
lemma perm_eq_refl_of_strictMono {m : ℕ} (σ : Perm (Fin m)) (hσ : StrictMono σ) :
    σ = Equiv.refl (Fin m) := by
  apply Equiv.ext
  intro i
  have h_symm_mono : StrictMono σ.symm := by
    intro a b hab
    by_contra h_not
    have h_ge : σ.symm b ≤ σ.symm a := not_lt.mp h_not
    rcases eq_or_lt_of_le h_ge with h_eq | h_lt
    · exact ne_of_lt hab (σ.symm.injective h_eq.symm)
    · have h_lt' : σ (σ.symm b) < σ (σ.symm a) := hσ h_lt
      rw [apply_symm_apply, apply_symm_apply] at h_lt'
      exact lt_asymm hab h_lt'
  have h1 : i.val ≤ (σ i).val := fin_val_le_of_strictMono σ hσ i.val i.isLt
  have h2 : (σ i).val ≤ (σ.symm (σ i)).val :=
    fin_val_le_of_strictMono σ.symm h_symm_mono (σ i).val (σ i).isLt
  rw [symm_apply_apply] at h2
  apply Fin.ext
  change (σ i).val = i.val
  omega

/-- **定理（斜分拆一般形式）：对任意单调不增共轭分拆 `μ, ν`，任何不相交的合法 0-1 格路簇必满足 `σ = Equiv.refl`** -/
theorem perm_eq_refl_of_nonIntersecting {m N : ℕ}
    (μ ν : Fin m → ℕ) (hμ : Antitone μ) (hν : Antitone ν)
    (σ : Perm (Fin m)) (u : Fin m → Fin (N + 1) → ℤ)
    (h_start : ∀ i : Fin m, u i 0 = (ν i : ℤ) - (i.val : ℤ))
    (h_end : ∀ i : Fin m, u i (Fin.last N) = (μ (σ i) : ℤ) - ((σ i).val : ℤ))
    (h_step : ∀ (i : Fin m) (t : Fin N),
      u i t.succ - u i t.castSucc = 0 ∨ u i t.succ - u i t.castSucc = 1)
    (h_disj : ∀ (t : Fin (N + 1)) (i j : Fin m), i < j → u i t ≠ u j t) :
    σ = Equiv.refl (Fin m) := by
  apply perm_eq_refl_of_strictMono σ
  intro i j hij
  have h0 : u j 0 < u i 0 := by
    rw [h_start i, h_start j]
    exact strictAnti_conjShift ν hν hij
  have hN : u j (Fin.last N) < u i (Fin.last N) :=
    nonIntersecting_gt_of_start_gt (u i) (u j) h0 (h_step i) (h_step j)
      (fun t => h_disj t i j hij) (Fin.last N)
  rw [h_end i, h_end j] at hN
  by_contra h_not_lt
  have h_ge : σ j ≤ σ i := not_lt.mp h_not_lt
  rcases eq_or_lt_of_le h_ge with h_eq | h_lt
  · rw [h_eq] at hN
    exact lt_irrefl _ hN
  · have h_anti : (μ (σ i) : ℤ) - ((σ i).val : ℤ) < (μ (σ j) : ℤ) - ((σ j).val : ℤ) :=
      strictAnti_conjShift μ hμ h_lt
    exact lt_asymm hN h_anti

/-! ### 4. 斜分拆格路配置空间 `PathConfig`、Gessel–Viennot 对合与抵消引理 -/

/-- 相交存在性谓词 -/
def HasIntersection {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ) : Prop :=
  ∃ t : Fin (N + 1), ∃ i : Fin m, ∃ j : Fin m, i < j ∧ u i t = u j t

instance {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ) : Decidable (HasIntersection u) := by
  unfold HasIntersection
  infer_instance

/-- 有界自然数上的最小元存在引理 -/
lemma exists_min_nat (B : ℕ) (P : ℕ → Prop) :
    (∃ k ≤ B, P k) → ∃ k₀ ≤ B, P k₀ ∧ ∀ k < k₀, ¬P k := by
  classical
  induction B with
  | zero =>
    rintro ⟨k, hk, hpk⟩
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨0, le_refl 0, hpk, fun k hk => by omega⟩
  | succ B ih =>
    intro h
    by_cases hB : ∃ k ≤ B, P k
    · rcases ih hB with ⟨k₀, hk₀, hpk₀, hmin⟩
      exact ⟨k₀, Nat.le_succ_of_le hk₀, hpk₀, hmin⟩
    · rcases h with ⟨k, hk, hpk⟩
      have hk_eq : k = B + 1 := by
        by_contra hne
        have hle : k ≤ B := by omega
        exact hB ⟨k, hle, hpk⟩
      subst hk_eq
      refine ⟨B + 1, le_refl (B + 1), hpk, fun k hk hp => ?_⟩
      have hle : k ≤ B := by omega
      exact hB ⟨k, hle, hp⟩

/-- `Fin n` 上的最小元存在引理 -/
lemma exists_min_fin {n : ℕ} (P : Fin n → Prop) (h : ∃ k : Fin n, P k) :
    ∃ k₀ : Fin n, P k₀ ∧ ∀ k < k₀, ¬P k := by
  rcases h with ⟨k_wit, hk_wit⟩
  let Q : ℕ → Prop := fun a => ∃ ha : a < n, P ⟨a, ha⟩
  have hQ : ∃ a ≤ k_wit.val, Q a := ⟨k_wit.val, le_refl _, k_wit.isLt, hk_wit⟩
  rcases exists_min_nat k_wit.val Q hQ with ⟨a₀, _, ⟨ha₀, hpa₀⟩, hmin⟩
  refine ⟨⟨a₀, ha₀⟩, hpa₀, fun k hk hpk => ?_⟩
  have hk_lt : k.val < a₀ := hk
  exact hmin k.val hk_lt ⟨k.isLt, hpk⟩

/-- 构造任意相交格路簇的唯一首交点三元组 `(t₀, i₀, j₀)` -/
lemma exists_firstIntersection {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ)
    (h : HasIntersection u) :
    ∃ t₀ i₀ j₀, IsFirstIntersection u t₀ i₀ j₀ := by
  rcases exists_min_fin (fun t : Fin (N + 1) => ∃ i j : Fin m, i < j ∧ u i t = u j t) h
    with ⟨t₀, ht₀, hmin_t⟩
  rcases exists_min_fin (fun i : Fin m => ∃ j : Fin m, i < j ∧ u i t₀ = u j t₀) ht₀
    with ⟨i₀, hi₀, hmin_i⟩
  rcases exists_min_fin (fun j : Fin m => i₀ < j ∧ u i₀ t₀ = u j t₀) hi₀
    with ⟨j₀, ⟨hij₀, heq₀⟩, hmin_j⟩
  refine ⟨t₀, i₀, j₀, hij₀, heq₀, ?_, ?_, ?_⟩
  · intro t ht i j hij heq
    exact hmin_t t ht ⟨i, j, hij, heq⟩
  · intro i hi j hij heq
    exact hmin_i i hi ⟨j, hij, heq⟩
  · intro j hj hij heq
    exact hmin_j j hj ⟨hij, heq⟩

/-- 提取相交格路簇的首交点时刻 `t₀` -/
def firstT {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ) (h : HasIntersection u) : Fin (N + 1) :=
  (exists_firstIntersection u h).choose

/-- 提取相交格路簇的首交点第一下标 `i₀` -/
def firstI {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ) (h : HasIntersection u) : Fin m :=
  (exists_firstIntersection u h).choose_spec.choose

/-- 提取相交格路簇的首交点第二下标 `j₀` -/
def firstJ {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ) (h : HasIntersection u) : Fin m :=
  (exists_firstIntersection u h).choose_spec.choose_spec.choose

/-- `(firstT u h, firstI u h, firstJ u h)` 满足 `IsFirstIntersection` -/
lemma firstIntersection_spec {m N : ℕ} (u : Fin m → Fin (N + 1) → ℤ) (h : HasIntersection u) :
    IsFirstIntersection u (firstT u h) (firstI u h) (firstJ u h) :=
  (exists_firstIntersection u h).choose_spec.choose_spec.choose_spec

/-- 对任意斜共轭分拆 `μ, ν`，定义行列式展开中的格路簇配置 `(σ, u)` -/
structure PathConfig (m N : ℕ) (μ ν : Fin m → ℕ) where
  σ : Perm (Fin m)
  u : Fin m → Fin (N + 1) → ℤ
  start_eq : ∀ i : Fin m, u i 0 = (ν i : ℤ) - (i.val : ℤ)
  end_eq : ∀ i : Fin m, u i (Fin.last N) = (μ (σ i) : ℤ) - ((σ i).val : ℤ)
  step_valid : ∀ (i : Fin m) (t : Fin N),
    u i t.succ - u i t.castSucc = 0 ∨ u i t.succ - u i t.castSucc = 1

@[ext]
lemma PathConfig.ext {m N : ℕ} {μ ν : Fin m → ℕ}
    {c₁ c₂ : PathConfig m N μ ν} (hσ : c₁.σ = c₂.σ) (hu : c₁.u = c₂.u) :
    c₁ = c₂ := by
  rcases c₁ with ⟨σ₁, u₁, _, _, _⟩
  rcases c₂ with ⟨σ₂, u₂, _, _, _⟩
  change σ₁ = σ₂ at hσ
  change u₁ = u₂ at hu
  subst hσ
  subst hu
  rfl

/-- 任何相交时刻 `t₀` 必然严格小于终点时刻 `Fin.last N` -/
lemma firstIntersection_lt_last {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) {t₀ : Fin (N + 1)} {i₀ j₀ : Fin m}
    (h : IsFirstIntersection c.u t₀ i₀ j₀) :
    ¬(Fin.last N ≤ t₀) := by
  intro h_le
  have ht_eq : t₀ = Fin.last N := by
    apply Fin.ext
    change N ≤ t₀.val at h_le
    have h_lt : t₀.val < N + 1 := t₀.isLt
    change t₀.val = N
    omega
  have h_end_eq : c.u i₀ (Fin.last N) = c.u j₀ (Fin.last N) := by
    rw [← ht_eq]; exact h.eq_at
  rw [c.end_eq i₀, c.end_eq j₀] at h_end_eq
  have h_ne : c.σ i₀ ≠ c.σ j₀ := c.σ.injective.ne (ne_of_lt h.lt_idx)
  rcases lt_or_gt_of_ne h_ne with hlt | hgt
  · exact ne_of_gt (strictAnti_conjShift μ hμ hlt) h_end_eq
  · exact ne_of_lt (strictAnti_conjShift μ hμ hgt) h_end_eq

/-- 在相交配置上定义 Gessel–Viennot 对合 `gvInvolution` -/
def gvInvolution {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) : PathConfig m N μ ν :=
  if h : HasIntersection c.u then
    { σ := c.σ * Equiv.swap (firstI c.u h) (firstJ c.u h)
      u := swapSuffix c.u (firstT c.u h) (firstI c.u h) (firstJ c.u h)
      start_eq := fun i => by
        have h0 : (0 : Fin (N + 1)) ≤ firstT c.u h := Fin.zero_le _
        rw [swapSuffix_le _ _ _ _ _ h0, c.start_eq i]
      end_eq := fun i => by
        have h_not_le : ¬(Fin.last N ≤ firstT c.u h) :=
          firstIntersection_lt_last hμ c (firstIntersection_spec c.u h)
        rw [swapSuffix_gt _ _ _ _ _ h_not_le, c.end_eq (Equiv.swap (firstI c.u h) (firstJ c.u h) i)]
        rfl
      step_valid := fun i t => by
        rw [step_swapSuffix c.u (firstT c.u h) (firstI c.u h) (firstJ c.u h)
            (firstIntersection_spec c.u h).eq_at i t]
        by_cases h_le : t.succ ≤ firstT c.u h
        · rw [ite_pos_eq h_le]
          exact c.step_valid i t
        · rw [ite_neg_eq h_le]
          exact c.step_valid (Equiv.swap (firstI c.u h) (firstJ c.u h) i) t }
  else c

lemma gvInvolution_σ_of_pos {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) (h : HasIntersection c.u) :
    (gvInvolution hμ c).σ = c.σ * Equiv.swap (firstI c.u h) (firstJ c.u h) := by
  unfold gvInvolution
  rw [dite_pos_eq h]

lemma gvInvolution_u_of_pos {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) (h : HasIntersection c.u) :
    (gvInvolution hμ c).u = swapSuffix c.u (firstT c.u h) (firstI c.u h) (firstJ c.u h) := by
  unfold gvInvolution
  rw [dite_pos_eq h]

lemma gvInvolution_of_neg {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) (h : ¬HasIntersection c.u) :
    gvInvolution hμ c = c := by
  unfold gvInvolution
  rw [dite_neg_eq h]

lemma gvInvolution_hasIntersection {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) (h : HasIntersection c.u) :
    HasIntersection (gvInvolution hμ c).u := by
  have h_first := firstIntersection_spec c.u h
  have h_first' : IsFirstIntersection (gvInvolution hμ c).u
      (firstT c.u h) (firstI c.u h) (firstJ c.u h) := by
    rw [gvInvolution_u_of_pos hμ c h]
    exact (IsFirstIntersection.swapSuffix_iff c.u _ _ _).mpr h_first
  exact ⟨firstT c.u h, firstI c.u h, firstJ c.u h, h_first'.lt_idx, h_first'.eq_at⟩

/-- **定理：`gvInvolution` 在所有配置上严格是对合（`gvInvolution (gvInvolution c) = c`）** -/
theorem gvInvolution_involutive {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) :
    gvInvolution hμ (gvInvolution hμ c) = c := by
  by_cases h : HasIntersection c.u
  · have h' : HasIntersection (gvInvolution hμ c).u :=
      gvInvolution_hasIntersection hμ c h
    have h_first : IsFirstIntersection (gvInvolution hμ c).u
        (firstT c.u h) (firstI c.u h) (firstJ c.u h) := by
      rw [gvInvolution_u_of_pos hμ c h]
      exact (IsFirstIntersection.swapSuffix_iff c.u _ _ _).mpr (firstIntersection_spec c.u h)
    have h_first' := firstIntersection_spec (gvInvolution hμ c).u h'
    rcases h_first'.unique h_first with ⟨ht, hi, hj⟩
    apply PathConfig.ext
    · rw [gvInvolution_σ_of_pos hμ (gvInvolution hμ c) h', hi, hj,
          gvInvolution_σ_of_pos hμ c h]
      apply Equiv.ext
      intro k
      exact congrArg c.σ (Equiv.swap_apply_self (firstI c.u h) (firstJ c.u h) k)
    · rw [gvInvolution_u_of_pos hμ (gvInvolution hμ c) h', ht, hi, hj,
          gvInvolution_u_of_pos hμ c h, swapSuffix_involutive]
  · rw [gvInvolution_of_neg hμ c h, gvInvolution_of_neg hμ c h]

/-- **定理：相交配置在 `gvInvolution` 下保持相交性、保持权重，且置换符号取反** -/
theorem gvInvolution_cancel {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (x : Fin N → R) (c : PathConfig m N μ ν) (h : HasIntersection c.u) :
    ((Perm.sign c.σ : ℤ) • pathFamilyWt x c.u) +
    ((Perm.sign (gvInvolution hμ c).σ : ℤ) • pathFamilyWt x (gvInvolution hμ c).u) = 0 := by
  have h_first := firstIntersection_spec c.u h
  have h_wt : pathFamilyWt x (gvInvolution hμ c).u = pathFamilyWt x c.u := by
    rw [gvInvolution_u_of_pos hμ c h]
    exact pathFamilyWt_swapSuffix x c.u _ _ _ h_first.eq_at
  have h_sign : (Perm.sign (gvInvolution hμ c).σ : ℤ) = -(Perm.sign c.σ : ℤ) := by
    rw [gvInvolution_σ_of_pos hμ c h, map_mul,
        Perm.sign_swap (ne_of_lt h_first.lt_idx), Units.val_mul]
    simp
  rw [h_wt, h_sign, neg_smul, add_neg_cancel]

/-- 配置相交谓词 -/
def isIntersecting {m N : ℕ} {μ ν : Fin m → ℕ} (c : PathConfig m N μ ν) : Prop :=
  HasIntersection c.u

instance {m N : ℕ} {μ ν : Fin m → ℕ} : DecidablePred (@isIntersecting m N μ ν) :=
  fun c => inferInstanceAs (Decidable (HasIntersection c.u))

/-- 相交配置的正半区判别谓词：在首交点处满足 `c.σ i₀ < c.σ j₀` -/
def isPosBad {m N : ℕ} {μ ν : Fin m → ℕ} (c : PathConfig m N μ ν) : Prop :=
  ∃ h : HasIntersection c.u, c.σ (firstI c.u h) < c.σ (firstJ c.u h)

instance {m N : ℕ} {μ ν : Fin m → ℕ} : DecidablePred (@isPosBad m N μ ν) :=
  fun c =>
    if h : HasIntersection c.u then
      decidable_of_iff (c.σ (firstI c.u h) < c.σ (firstJ c.u h))
        ⟨fun hlt => ⟨h, hlt⟩, fun ⟨_, hlt⟩ => hlt⟩
    else
      isFalse (fun ⟨h', _⟩ => h h')

/-- 正半区相交配置在 `gvInvolution` 作用下必进入负半区 -/
lemma not_isPosBad_gvInvolution {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) (h : HasIntersection c.u) (hp : isPosBad c) :
    ¬isPosBad (gvInvolution hμ c) := by
  rcases hp with ⟨_, hlt⟩
  rintro ⟨h', hlt'⟩
  have h_first : IsFirstIntersection (gvInvolution hμ c).u
      (firstT c.u h) (firstI c.u h) (firstJ c.u h) := by
    rw [gvInvolution_u_of_pos hμ c h]
    exact (IsFirstIntersection.swapSuffix_iff c.u _ _ _).mpr (firstIntersection_spec c.u h)
  rcases (firstIntersection_spec (gvInvolution hμ c).u h').unique h_first with ⟨_, hi, hj⟩
  rw [hi, hj, gvInvolution_σ_of_pos hμ c h] at hlt'
  change c.σ (Equiv.swap (firstI c.u h) (firstJ c.u h) (firstI c.u h)) <
         c.σ (Equiv.swap (firstI c.u h) (firstJ c.u h) (firstJ c.u h)) at hlt'
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at hlt'
  exact lt_asymm hlt hlt'

/-- 负半区相交配置在 `gvInvolution` 作用下必进入正半区 -/
lemma isPosBad_gvInvolution_of_not {m N : ℕ} {μ ν : Fin m → ℕ} (hμ : Antitone μ)
    (c : PathConfig m N μ ν) (h : HasIntersection c.u) (hnp : ¬isPosBad c) :
    isPosBad (gvInvolution hμ c) := by
  have h' : HasIntersection (gvInvolution hμ c).u := gvInvolution_hasIntersection hμ c h
  refine ⟨h', ?_⟩
  have h_first := firstIntersection_spec c.u h
  have h_first_gv : IsFirstIntersection (gvInvolution hμ c).u
      (firstT c.u h) (firstI c.u h) (firstJ c.u h) := by
    rw [gvInvolution_u_of_pos hμ c h]
    exact (IsFirstIntersection.swapSuffix_iff c.u _ _ _).mpr h_first
  rcases (firstIntersection_spec (gvInvolution hμ c).u h').unique h_first_gv with ⟨_, hi, hj⟩
  rw [hi, hj, gvInvolution_σ_of_pos hμ c h]
  change c.σ (Equiv.swap (firstI c.u h) (firstJ c.u h) (firstI c.u h)) <
         c.σ (Equiv.swap (firstI c.u h) (firstJ c.u h) (firstJ c.u h))
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases lt_trichotomy (c.σ (firstI c.u h)) (c.σ (firstJ c.u h)) with hlt | heq | hgt
  · exact absurd ⟨h, hlt⟩ hnp
  · exact absurd (c.σ.injective heq) (ne_of_lt h_first.lt_idx)
  · exact hgt

/-- **Gessel–Viennot 抵消定理（斜分拆一般形式）** -/
theorem gv_cancellation_complete {m N : ℕ} {μ ν : Fin m → ℕ}
    (hμ : Antitone μ) (hν : Antitone ν)
    (x : Fin N → R) (U : Finset (PathConfig m N μ ν))
    (hU_closed : ∀ c ∈ U, gvInvolution hμ c ∈ U) :
    (∑ c ∈ U, (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u) =
    (∑ c ∈ U.filter (fun c => ¬isIntersecting c), pathFamilyWt x c.u) := by
  rw [sum_split_filter U isIntersecting]
  have h_bad_zero :
      (∑ c ∈ U.filter isIntersecting,
        (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u) = 0 := by
    rw [sum_split_filter (U.filter isIntersecting) isPosBad]
    have h_bij :
        (∑ c ∈ (U.filter isIntersecting).filter (fun c => ¬isPosBad c),
          (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u) =
        (∑ c ∈ (U.filter isIntersecting).filter isPosBad,
          (Perm.sign (gvInvolution hμ c).σ : ℤ) • pathFamilyWt x (gvInvolution hμ c).u) := by
      refine sum_reindex_involutive
        ((U.filter isIntersecting).filter isPosBad)
        ((U.filter isIntersecting).filter (fun c => ¬isPosBad c))
        (gvInvolution hμ)
        (fun c => (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u)
        (gvInvolution_involutive hμ) ?_ ?_
      · intro c hc
        rcases Finset.mem_filter.mp hc with ⟨hc_bad, hc_pos⟩
        rcases Finset.mem_filter.mp hc_bad with ⟨hc_U, h_int⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hU_closed c hc_U, gvInvolution_hasIntersection hμ c h_int⟩,
           not_isPosBad_gvInvolution hμ c h_int hc_pos⟩
      · intro c hc
        rcases Finset.mem_filter.mp hc with ⟨hc_bad, hc_neg⟩
        rcases Finset.mem_filter.mp hc_bad with ⟨hc_U, h_int⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hU_closed c hc_U, gvInvolution_hasIntersection hμ c h_int⟩,
           isPosBad_gvInvolution_of_not hμ c h_int hc_neg⟩
    rw [h_bij, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun c hc => ?_)
    have h_int : HasIntersection c.u :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    exact gvInvolution_cancel hμ x c h_int
  have h_ssyt :
      (∑ c ∈ U.filter (fun c => ¬isIntersecting c),
        (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u) =
      (∑ c ∈ U.filter (fun c => ¬isIntersecting c), pathFamilyWt x c.u) := by
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have h_no_int : ¬HasIntersection c.u := (Finset.mem_filter.mp hc).2
    have h_disj : ∀ (t : Fin (N + 1)) (i j : Fin m), i < j → c.u i t ≠ c.u j t := by
      intro t i j hij heq
      exact h_no_int ⟨t, i, j, hij, heq⟩
    have h_refl : c.σ = 1 :=
      perm_eq_refl_of_nonIntersecting μ ν hμ hν c.σ c.u c.start_eq c.end_eq c.step_valid h_disj
    rw [h_refl, map_one, Units.val_one, one_smul]
  rw [h_bad_zero, zero_add, h_ssyt]

/-! ### 5. 桥 B1：路径 `elemSymm` 与标准子集求和初等对称多项式 `esymmPoly` 的等价性 -/

/-- 起点与单步增量均相同的两条格路必相等 -/
lemma path_eq_of_steps_eq {N : ℕ} (p₁ p₂ : Fin (N + 1) → ℤ)
    (h0 : p₁ 0 = p₂ 0)
    (hstep : ∀ t : Fin N, p₁ t.succ - p₁ t.castSucc = p₂ t.succ - p₂ t.castSucc) :
    p₁ = p₂ := by
  funext t
  induction t using Fin.induction with
  | zero => exact h0
  | succ t ih =>
    change p₁ t.castSucc = p₂ t.castSucc at ih
    have hs := hstep t
    omega

/-- 从整数起点 `a` 到终点 `b` 的单条 `N` 步 0-1 格路 -/
structure SinglePath (N : ℕ) (a b : ℤ) where
  p : Fin (N + 1) → ℤ
  start_eq : p 0 = a
  end_eq : p (Fin.last N) = b
  step_valid : ∀ t : Fin N, p t.succ - p t.castSucc = 0 ∨ p t.succ - p t.castSucc = 1

@[ext]
lemma SinglePath.ext {N : ℕ} {a b : ℤ} {sp₁ sp₂ : SinglePath N a b}
    (hp : sp₁.p = sp₂.p) : sp₁ = sp₂ := by
  rcases sp₁ with ⟨p₁, _, _, _⟩
  rcases sp₂ with ⟨p₂, _, _, _⟩
  change p₁ = p₂ at hp
  subst hp
  rfl

/-- 将单条 0-1 格路编码为布尔步长向量 `Fin N → Bool` -/
def singlePathToBool {N : ℕ} {a b : ℤ} (sp : SinglePath N a b) : Fin N → Bool :=
  fun t => if sp.p t.succ - sp.p t.castSucc = 1 then true else false

lemma singlePathToBool_injective {N : ℕ} {a b : ℤ} :
    Function.Injective (@singlePathToBool N a b) := by
  intro sp₁ sp₂ h
  apply SinglePath.ext
  apply path_eq_of_steps_eq sp₁.p sp₂.p (sp₁.start_eq.trans sp₂.start_eq.symm)
  intro t
  have ht : singlePathToBool sp₁ t = singlePathToBool sp₂ t := congrFun h t
  change (if sp₁.p t.succ - sp₁.p t.castSucc = 1 then true else false) =
         (if sp₂.p t.succ - sp₂.p t.castSucc = 1 then true else false) at ht
  rcases sp₁.step_valid t with h1 | h1 <;> rcases sp₂.step_valid t with h2 | h2
  · omega
  · have hne : sp₁.p t.succ - sp₁.p t.castSucc ≠ 1 := by omega
    rw [ite_neg_eq hne, ite_pos_eq h2] at ht
    cases ht
  · have hne : sp₂.p t.succ - sp₂.p t.castSucc ≠ 1 := by omega
    rw [ite_pos_eq h1, ite_neg_eq hne] at ht
    cases ht
  · omega

instance {N : ℕ} {a b : ℤ} : Fintype (SinglePath N a b) :=
  Fintype.ofInjective singlePathToBool singlePathToBool_injective

/-- 单条 0-1 格路的单项式权重 -/
def singlePathWt {N : ℕ} (x : Fin N → R) {a b : ℤ} (sp : SinglePath N a b) : R :=
  ∏ t : Fin N, stepWt x t (sp.p t.succ - sp.p t.castSucc)

/-- 格路定义的初等对称多项式 `elemSymm` -/
def elemSymm (N : ℕ) (x : Fin N → R) (r : ℤ) : R :=
  ∑ sp : SinglePath N 0 r, singlePathWt x sp

/-- **标准子集求和定义的初等对称多项式 `esymmPoly`**（与 `MvPolynomial.esymm` 定义一致） -/
def esymmPoly (N : ℕ) (x : Fin N → R) (r : ℤ) : R :=
  if r < 0 then 0
  else ∑ S ∈ Finset.powersetCard r.toNat (Finset.univ : Finset (Fin N)), ∏ t ∈ S, x t

/-- 从子集 `S : Finset (Fin N)` 构造前缀和格路 -/
def subsetToPathFun {N : ℕ} (S : Finset (Fin N)) (t : Fin (N + 1)) : ℤ :=
  ∑ s ∈ S, if s.val < t.val then (1 : ℤ) else 0

lemma subsetToPathFun_zero {N : ℕ} (S : Finset (Fin N)) :
    subsetToPathFun S 0 = 0 := by
  unfold subsetToPathFun
  refine Finset.sum_eq_zero (fun s _ => ?_)
  have h_not_lt : ¬(s.val < (0 : Fin (N + 1)).val) := by
    change ¬(s.val < 0)
    omega
  exact ite_neg_eq h_not_lt (1 : ℤ) 0

lemma subsetToPathFun_last {N : ℕ} (S : Finset (Fin N)) :
    subsetToPathFun S (Fin.last N) = (S.card : ℤ) := by
  unfold subsetToPathFun
  have h_one : ∀ s ∈ S, (if s.val < (Fin.last N).val then (1 : ℤ) else 0) = 1 := by
    intro s _
    have h_lt : s.val < (Fin.last N).val := s.isLt
    exact ite_pos_eq h_lt (1 : ℤ) 0
  rw [Finset.sum_congr rfl h_one]
  simp

lemma subsetToPathFun_step {N : ℕ} (S : Finset (Fin N)) (t : Fin N) :
    subsetToPathFun S t.succ - subsetToPathFun S t.castSucc =
    if t ∈ S then 1 else 0 := by
  unfold subsetToPathFun
  rw [← Finset.sum_sub_distrib]
  have h_term : ∀ s ∈ S,
      ((if s.val < t.succ.val then (1 : ℤ) else 0) -
       (if s.val < t.castSucc.val then (1 : ℤ) else 0)) =
      if s = t then 1 else 0 := by
    intro s _
    by_cases h_eq : s = t
    · subst h_eq
      have h1 : s.val < s.succ.val := by
        change s.val < s.val + 1
        omega
      have h2 : ¬(s.val < s.castSucc.val) := by
        change ¬(s.val < s.val)
        omega
      rw [ite_pos_eq h1, ite_neg_eq h2, ite_pos_eq rfl]
      omega
    · have h_ne_val : s.val ≠ t.val := fun h => h_eq (Fin.ext h)
      by_cases h_lt : s.val < t.castSucc.val
      · have h_lt1 : s.val < t.succ.val := by
          change s.val < t.val at h_lt
          change s.val < t.val + 1
          omega
        rw [ite_pos_eq h_lt1, ite_pos_eq h_lt, ite_neg_eq h_eq]
        omega
      · have h_nlt1 : ¬(s.val < t.succ.val) := by
          change ¬(s.val < t.val) at h_lt
          change ¬(s.val < t.val + 1)
          omega
        rw [ite_neg_eq h_nlt1, ite_neg_eq h_lt, ite_neg_eq h_eq]
        omega
  rw [Finset.sum_congr rfl h_term]
  by_cases ht : t ∈ S
  · rw [ite_pos_eq ht, Finset.sum_eq_single t]
    · exact ite_pos_eq rfl (1 : ℤ) 0
    · intro s _ hst
      exact ite_neg_eq hst (1 : ℤ) 0
    · intro h_abs
      exact absurd ht h_abs
  · rw [ite_neg_eq ht]
    refine Finset.sum_eq_zero (fun s hs => ?_)
    have hne : s ≠ t := fun h_eq => ht (h_eq ▸ hs)
    exact ite_neg_eq hne (1 : ℤ) 0

/-- 从单条格路提取步长为 1 的时刻子集 `pathToSubset` -/
def pathToSubset {N : ℕ} {r : ℤ} (sp : SinglePath N 0 r) : Finset (Fin N) :=
  Finset.univ.filter (fun t : Fin N => sp.p t.succ - sp.p t.castSucc = 1)

lemma subsetToPathFun_pathToSubset {N : ℕ} {r : ℤ} (sp : SinglePath N 0 r) :
    subsetToPathFun (pathToSubset sp) = sp.p := by
  apply path_eq_of_steps_eq _ _ ((subsetToPathFun_zero _).trans sp.start_eq.symm)
  intro t
  rw [subsetToPathFun_step]
  by_cases h1 : sp.p t.succ - sp.p t.castSucc = 1
  · have ht : t ∈ pathToSubset sp :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ t, h1⟩
    rw [ite_pos_eq ht, h1]
  · have ht : t ∉ pathToSubset sp :=
      fun hm => h1 (Finset.mem_filter.mp hm).2
    rw [ite_neg_eq ht]
    rcases sp.step_valid t with h0 | h1'
    · omega
    · exact absurd h1' h1

lemma card_pathToSubset {N : ℕ} {r : ℤ} (sp : SinglePath N 0 r) :
    ((pathToSubset sp).card : ℤ) = r := by
  have h_eq := congrFun (subsetToPathFun_pathToSubset sp) (Fin.last N)
  rw [subsetToPathFun_last, sp.end_eq] at h_eq
  exact h_eq

lemma singlePathWt_eq_prod_pathToSubset {N : ℕ} (x : Fin N → R) {r : ℤ}
    (sp : SinglePath N 0 r) :
    singlePathWt x sp = ∏ t ∈ pathToSubset sp, x t := by
  unfold singlePathWt pathToSubset stepWt
  rw [Finset.prod_filter]

/-- **定理（桥 B1）：格路定义的 `elemSymm` 与标准子集求和定义的 `esymmPoly` 完全相等** -/
theorem elemSymm_eq_esymmPoly (N : ℕ) (x : Fin N → R) (r : ℤ) :
    elemSymm N x r = esymmPoly N x r := by
  unfold elemSymm esymmPoly
  by_cases hr : r < 0
  · rw [ite_pos_eq hr]
    refine Finset.sum_eq_zero (fun sp _ => ?_)
    have h_card := card_pathToSubset sp
    omega
  · rw [ite_neg_eq hr]
    have h_img :
        Finset.powersetCard r.toNat (Finset.univ : Finset (Fin N)) =
        (Finset.univ : Finset (SinglePath N 0 r)).image pathToSubset := by
      ext S
      rw [Finset.mem_powersetCard, Finset.mem_image]
      constructor
      · rintro ⟨_, hcard⟩
        let sp : SinglePath N 0 r :=
          { p := subsetToPathFun S
            start_eq := subsetToPathFun_zero S
            end_eq := by
              rw [subsetToPathFun_last, hcard]
              omega
            step_valid := fun t => by
              rw [subsetToPathFun_step]
              by_cases ht : t ∈ S
              · right; exact ite_pos_eq ht 1 0
              · left; exact ite_neg_eq ht 1 0 }
        refine ⟨sp, Finset.mem_univ sp, ?_⟩
        ext t
        rw [pathToSubset, Finset.mem_filter]
        change (t ∈ Finset.univ ∧ subsetToPathFun S t.succ - subsetToPathFun S t.castSucc = 1) ↔ t ∈ S
        rw [subsetToPathFun_step]
        constructor
        · rintro ⟨_, h_one⟩
          by_cases ht : t ∈ S
          · exact ht
          · rw [ite_neg_eq ht] at h_one
            omega
        · intro ht
          exact ⟨Finset.mem_univ t, ite_pos_eq ht 1 0⟩
      · rintro ⟨sp, _, rfl⟩
        refine ⟨Finset.subset_univ _, ?_⟩
        have h_card := card_pathToSubset sp
        omega
    have h_sum1 :
        (∑ S ∈ Finset.powersetCard r.toNat (Finset.univ : Finset (Fin N)), ∏ t ∈ S, x t) =
        ∑ sp : SinglePath N 0 r, ∏ t ∈ pathToSubset sp, x t := by
      rw [h_img, Finset.sum_image]
      intro sp₁ _ sp₂ _ h_eq
      apply SinglePath.ext
      rw [← subsetToPathFun_pathToSubset sp₁, ← subsetToPathFun_pathToSubset sp₂, h_eq]
    rw [h_sum1]
    exact Finset.sum_congr rfl (fun sp _ => singlePathWt_eq_prod_pathToSubset x sp)

/-- 格路起点平移双射：`SinglePath N a b ≃ SinglePath N 0 (b - a)` -/
def shiftSinglePathEquiv (N : ℕ) (a b : ℤ) :
    SinglePath N a b ≃ SinglePath N 0 (b - a) where
  toFun sp :=
    { p := fun t => sp.p t - a
      start_eq := by have := sp.start_eq; omega
      end_eq := by have := sp.end_eq; omega
      step_valid := fun t => by
        have h_diff : (sp.p t.succ - a) - (sp.p t.castSucc - a) =
                      sp.p t.succ - sp.p t.castSucc := by omega
        rw [h_diff]
        exact sp.step_valid t }
  invFun sp :=
    { p := fun t => sp.p t + a
      start_eq := by have := sp.start_eq; omega
      end_eq := by have := sp.end_eq; omega
      step_valid := fun t => by
        have h_diff : (sp.p t.succ + a) - (sp.p t.castSucc + a) =
                      sp.p t.succ - sp.p t.castSucc := by omega
        rw [h_diff]
        exact sp.step_valid t }
  left_inv sp := by
    apply SinglePath.ext
    funext t
    change (sp.p t - a) + a = sp.p t
    omega
  right_inv sp := by
    apply SinglePath.ext
    funext t
    change (sp.p t + a) - a = sp.p t
    omega

/-- 从 `a` 到 `b` 的所有 0-1 格路权重之和等于标准初等对称多项式 `esymmPoly N x (b - a)` -/
lemma sum_singlePathWt_eq_esymmPoly {N : ℕ} (x : Fin N → R) (a b : ℤ) :
    (∑ sp : SinglePath N a b, singlePathWt x sp) = esymmPoly N x (b - a) := by
  rw [← elemSymm_eq_esymmPoly]
  unfold elemSymm
  refine sum_univ_equiv (shiftSinglePathEquiv N a b)
    (singlePathWt x) (singlePathWt x) (fun sp => ?_)
  unfold singlePathWt
  refine Finset.prod_congr rfl (fun t _ => ?_)
  change stepWt x t (sp.p t.succ - sp.p t.castSucc) =
         stepWt x t ((sp.p t.succ - a) - (sp.p t.castSucc - a))
  have h_diff : (sp.p t.succ - a) - (sp.p t.castSucc - a) =
                sp.p t.succ - sp.p t.castSucc := by omega
  rw [h_diff]

/-! ### 6. 左桥：斜分拆第二 Jacobi–Trudi 矩阵行列式展开 -/

/-- **斜分拆第二 Jacobi–Trudi 矩阵**：第 `(i, j)` 项为标准初等对称多项式 `e_{μ_i - ν_j - i + j}(x)` -/
def jacobiTrudiMatrix {m N : ℕ} (μ ν : Fin m → ℕ) (x : Fin N → R) :
    Matrix (Fin m) (Fin m) R :=
  fun i j => esymmPoly N x ((μ i : ℤ) - (ν j : ℤ) - (i.val : ℤ) + (j.val : ℤ))

lemma jacobiTrudiMatrix_apply {m N : ℕ} (μ ν : Fin m → ℕ) (x : Fin N → R) (i j : Fin m) :
    jacobiTrudiMatrix μ ν x i j =
    ∑ sp : SinglePath N ((ν j : ℤ) - (j.val : ℤ)) ((μ i : ℤ) - (i.val : ℤ)),
      singlePathWt x sp := by
  unfold jacobiTrudiMatrix
  rw [sum_singlePathWt_eq_esymmPoly]
  have h_idx : ((μ i : ℤ) - (i.val : ℤ)) - ((ν j : ℤ) - (j.val : ℤ)) =
               (μ i : ℤ) - (ν j : ℤ) - (i.val : ℤ) + (j.val : ℤ) := by omega
  rw [h_idx]

/-- 将配置 `PathConfig m N μ ν` 编码为 `(σ, 步长布尔矩阵)` 以导出 `Fintype` 实例 -/
def pathConfigToCode {m N : ℕ} {μ ν : Fin m → ℕ} (c : PathConfig m N μ ν) :
    Perm (Fin m) × (Fin m → Fin N → Bool) :=
  (c.σ, fun i t => if c.u i t.succ - c.u i t.castSucc = 1 then true else false)

lemma pathConfigToCode_injective {m N : ℕ} {μ ν : Fin m → ℕ} :
    Function.Injective (@pathConfigToCode m N μ ν) := by
  intro c₁ c₂ h
  have hσ : c₁.σ = c₂.σ := congrArg Prod.fst h
  have hcode : (pathConfigToCode c₁).2 = (pathConfigToCode c₂).2 := congrArg Prod.snd h
  apply PathConfig.ext hσ
  funext i
  apply path_eq_of_steps_eq (c₁.u i) (c₂.u i) ((c₁.start_eq i).trans (c₂.start_eq i).symm)
  intro t
  have ht : (pathConfigToCode c₁).2 i t = (pathConfigToCode c₂).2 i t :=
    congrFun (congrFun hcode i) t
  change (if c₁.u i t.succ - c₁.u i t.castSucc = 1 then true else false) =
         (if c₂.u i t.succ - c₂.u i t.castSucc = 1 then true else false) at ht
  rcases c₁.step_valid i t with h1 | h1 <;> rcases c₂.step_valid i t with h2 | h2
  · omega
  · have hne : c₁.u i t.succ - c₁.u i t.castSucc ≠ 1 := by omega
    rw [ite_neg_eq hne, ite_pos_eq h2] at ht
    cases ht
  · have hne : c₂.u i t.succ - c₂.u i t.castSucc ≠ 1 := by omega
    rw [ite_pos_eq h1, ite_neg_eq hne] at ht
    cases ht
  · omega

instance {m N : ℕ} {μ ν : Fin m → ℕ} : Fintype (PathConfig m N μ ν) :=
  Fintype.ofInjective pathConfigToCode pathConfigToCode_injective

/-- 行列式展开项的依赖对类型 `(σ, f)` 与 `PathConfig m N μ ν` 之间的典范双射 -/
def configSigmaEquiv (m N : ℕ) (μ ν : Fin m → ℕ) :
    (Σ σ : Perm (Fin m),
      ∀ k : Fin m, SinglePath N ((ν k : ℤ) - (k.val : ℤ)) ((μ (σ k) : ℤ) - ((σ k).val : ℤ))) ≃
    PathConfig m N μ ν where
  toFun s :=
    { σ := s.1
      u := fun k t => (s.2 k).p t
      start_eq := fun k => (s.2 k).start_eq
      end_eq := fun k => (s.2 k).end_eq
      step_valid := fun k t => (s.2 k).step_valid t }
  invFun c :=
    ⟨c.σ, fun k =>
      { p := c.u k
        start_eq := c.start_eq k
        end_eq := c.end_eq k
        step_valid := c.step_valid k }⟩
  left_inv s := by rcases s with ⟨_, _⟩; rfl
  right_inv c := by rcases c with ⟨_, _, _, _, _⟩; rfl

/-- **左桥定理**：斜分拆第二 Jacobi–Trudi 矩阵的行列式等于全配置空间 `PathConfig m N μ ν` 上的带符号权重和 -/
theorem det_jacobiTrudiMatrix_eq_sum_pathConfig {m N : ℕ} (μ ν : Fin m → ℕ) (x : Fin N → R) :
    (jacobiTrudiMatrix μ ν x).det =
    ∑ c : PathConfig m N μ ν, (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u := by
  rw [Matrix.det_apply']
  have h_entry : ∀ σ : Perm (Fin m),
      (↑↑(Perm.sign σ) : R) * (∏ k : Fin m, jacobiTrudiMatrix μ ν x (σ k) k) =
      ∑ f : (∀ k : Fin m, SinglePath N ((ν k : ℤ) - (k.val : ℤ)) ((μ (σ k) : ℤ) - ((σ k).val : ℤ))),
        (Perm.sign σ : ℤ) • pathFamilyWt x (fun k t => (f k).p t) := by
    intro σ
    have h_prod :
        (∏ k : Fin m, jacobiTrudiMatrix μ ν x (σ k) k) =
        ∑ f : (∀ k : Fin m, SinglePath N ((ν k : ℤ) - (k.val : ℤ)) ((μ (σ k) : ℤ) - ((σ k).val : ℤ))),
          pathFamilyWt x (fun k t => (f k).p t) := by
      simp_rw [jacobiTrudiMatrix_apply]
      rw [Finset.prod_univ_sum]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      dsimp only [singlePathWt, pathFamilyWt]
      exact Finset.prod_comm
    rw [← zsmul_eq_mul, h_prod, Finset.smul_sum]
  simp_rw [h_entry]
  let F : (Σ σ : Perm (Fin m),
      ∀ k : Fin m, SinglePath N ((ν k : ℤ) - (k.val : ℤ)) ((μ (σ k) : ℤ) - ((σ k).val : ℤ))) → R :=
    fun s => (Perm.sign s.1 : ℤ) • pathFamilyWt x (fun k t => (s.2 k).p t)
  change (∑ σ : Perm (Fin m), ∑ f : _, F ⟨σ, f⟩) = _
  have h_sig : (∑ σ : Perm (Fin m), ∑ f : _, F ⟨σ, f⟩) = ∑ s : _, F s := by
    rw [← Finset.sum_sigma]
    rfl
  rw [h_sig]
  exact sum_univ_equiv (configSigmaEquiv m N μ ν) F
    (fun c => (Perm.sign c.σ : ℤ) • pathFamilyWt x c.u)
    (fun _ => rfl)

/-! ### 7. 右桥与桥 B2：斜半标准杨表 `SkewSSYT`、格点填数反演与主定理 -/

/-- **斜半标准杨表（Skew SSYT）**：外共轭分拆为 `μ = λ'`，内共轭分拆为 `ν = ν'` -/
structure SkewSSYT (m N : ℕ) (μ ν : Fin m → ℕ) where
  u : Fin m → Fin (N + 1) → ℤ
  start_eq : ∀ i : Fin m, u i 0 = (ν i : ℤ) - (i.val : ℤ)
  end_eq : ∀ i : Fin m, u i (Fin.last N) = (μ i : ℤ) - (i.val : ℤ)
  step_valid : ∀ (i : Fin m) (t : Fin N),
    u i t.succ - u i t.castSucc = 0 ∨ u i t.succ - u i t.castSucc = 1
  row_weak : ∀ (t : Fin (N + 1)) (i j : Fin m), i < j → u j t < u i t

@[ext]
lemma SkewSSYT.ext {m N : ℕ} {μ ν : Fin m → ℕ} {T₁ T₂ : SkewSSYT m N μ ν}
    (hu : T₁.u = T₂.u) : T₁ = T₂ := by
  rcases T₁ with ⟨u₁, _, _, _, _⟩
  rcases T₂ with ⟨u₂, _, _, _, _⟩
  change u₁ = u₂ at hu
  subst hu
  rfl

def skewSSYTToPaths {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν) :
    ∀ i : Fin m, SinglePath N ((ν i : ℤ) - (i.val : ℤ)) ((μ i : ℤ) - (i.val : ℤ)) :=
  fun i => ⟨T.u i, T.start_eq i, T.end_eq i, T.step_valid i⟩

lemma skewSSYTToPaths_injective {m N : ℕ} {μ ν : Fin m → ℕ} :
    Function.Injective (@skewSSYTToPaths m N μ ν) := by
  intro T₁ T₂ h
  apply SkewSSYT.ext
  funext i t
  have hi : (skewSSYTToPaths T₁ i).p = (skewSSYTToPaths T₂ i).p :=
    congrArg SinglePath.p (congrFun h i)
  exact congrFun hi t

instance {m N : ℕ} {μ ν : Fin m → ℕ} : Fintype (SkewSSYT m N μ ν) :=
  Fintype.ofInjective skewSSYTToPaths skewSSYTToPaths_injective

/-- **斜 Schur 多项式 `s_{λ/ν}(x_0, ..., x_{N-1})`** -/
def skewSchurPoly {m N : ℕ} (μ ν : Fin m → ℕ) (x : Fin N → R) : R :=
  ∑ T : SkewSSYT m N μ ν, pathFamilyWt x T.u

/-- 将 `SkewSSYT` 嵌入配置空间 `PathConfig`（取恒等置换 `σ = Equiv.refl`） -/
def skewSSYTToConfig {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν) :
    PathConfig m N μ ν where
  σ := Equiv.refl (Fin m)
  u := T.u
  start_eq := T.start_eq
  end_eq := T.end_eq
  step_valid := T.step_valid

/-- **右桥定理**：不相交配置子集上的格路簇权重和精确等于斜 Schur 多项式 `skewSchurPoly μ ν x` -/
theorem sum_nonIntersecting_eq_skewSchurPoly {m N : ℕ} {μ ν : Fin m → ℕ}
    (hμ : Antitone μ) (hν : Antitone ν) (x : Fin N → R) :
    (∑ c ∈ (Finset.univ : Finset (PathConfig m N μ ν)).filter (fun c => ¬isIntersecting c),
      pathFamilyWt x c.u) =
    skewSchurPoly μ ν x := by
  classical
  unfold skewSchurPoly
  have h_img :
      (Finset.univ : Finset (PathConfig m N μ ν)).filter (fun c => ¬isIntersecting c) =
      (Finset.univ : Finset (SkewSSYT m N μ ν)).image skewSSYTToConfig := by
    ext c
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, h_no_int⟩
      have h_disj : ∀ (t : Fin (N + 1)) (i j : Fin m), i < j → c.u i t ≠ c.u j t :=
        fun t i j hij heq => h_no_int ⟨t, i, j, hij, heq⟩
      have h_refl : c.σ = Equiv.refl (Fin m) :=
        perm_eq_refl_of_nonIntersecting μ ν hμ hν c.σ c.u c.start_eq c.end_eq c.step_valid h_disj
      let T : SkewSSYT m N μ ν :=
        { u := c.u
          start_eq := c.start_eq
          end_eq := fun i => by
            have h_end := c.end_eq i
            rw [h_refl] at h_end
            exact h_end
          step_valid := c.step_valid
          row_weak := fun t i j hij => by
            have h0 : c.u j 0 < c.u i 0 := by
              rw [c.start_eq i, c.start_eq j]
              exact strictAnti_conjShift ν hν hij
            exact nonIntersecting_gt_of_start_gt (c.u i) (c.u j) h0
              (c.step_valid i) (c.step_valid j) (fun s => h_disj s i j hij) t }
      refine ⟨T, Finset.mem_univ T, ?_⟩
      exact PathConfig.ext h_refl.symm rfl
    · rintro ⟨T, _, rfl⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨t, i, j, hij, heq⟩
      exact ne_of_gt (T.row_weak t i j hij) heq
  rw [h_img, Finset.sum_image]
  · rfl
  · intro T₁ _ T₂ _ h_eq
    exact SkewSSYT.ext (congrArg PathConfig.u h_eq)

/-- **桥 B2（格点填数反演）**：对斜杨图第 `i` 列第 `r` 行的合法方格（满足 `ν i ≤ r < μ i`），
    证明存在时刻 `t : Fin N` 使得第 `i` 列的累积计数 `u i t.succ + i` 越过阈值 `r` -/
lemma exists_cellEntry {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν)
    (i : Fin m) (r : ℕ) (hr_ge : ν i ≤ r) (hr_lt : r < μ i) :
    ∃ t : Fin N, (r : ℤ) < T.u i t.succ + (i.val : ℤ) := by
  cases N with
  | zero =>
    have h0 := T.start_eq i
    have hN := T.end_eq i
    have h_eq : (0 : Fin 1) = Fin.last 0 := rfl
    rw [h_eq, hN] at h0
    omega
  | succ N' =>
    refine ⟨Fin.last N', ?_⟩
    have h_succ : (Fin.last N').succ = Fin.last (N' + 1) := rfl
    rw [h_succ, T.end_eq i]
    omega

/-- 提取斜杨表 `T` 在第 `i` 列、第 `r` 行合法方格（`ν i ≤ r < μ i`）的填数 `cellEntry ∈ Fin N` -/
def cellEntry {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν)
    (i : Fin m) (r : ℕ) (hr_ge : ν i ≤ r) (hr_lt : r < μ i) : Fin N :=
  (exists_min_fin (fun t : Fin N => (r : ℤ) < T.u i t.succ + (i.val : ℤ))
    (exists_cellEntry T i r hr_ge hr_lt)).choose

lemma cellEntry_spec {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν)
    (i : Fin m) (r : ℕ) (hr_ge : ν i ≤ r) (hr_lt : r < μ i) :
    (r : ℤ) < T.u i (cellEntry T i r hr_ge hr_lt).succ + (i.val : ℤ) ∧
    ∀ t < cellEntry T i r hr_ge hr_lt, ¬((r : ℤ) < T.u i t.succ + (i.val : ℤ)) :=
  (exists_min_fin (fun t : Fin N => (r : ℤ) < T.u i t.succ + (i.val : ℤ))
    (exists_cellEntry T i r hr_ge hr_lt)).choose_spec

/-- 在时刻 `t = cellEntry T i r` 处，累积计数恰好从 `r` 跃升至 `r + 1` -/
lemma cellEntry_exact_val {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν)
    (i : Fin m) (r : ℕ) (hr_ge : ν i ≤ r) (hr_lt : r < μ i) :
    T.u i (cellEntry T i r hr_ge hr_lt).succ + (i.val : ℤ) = (r : ℤ) + 1 := by
  rcases cellEntry_spec T i r hr_ge hr_lt with ⟨h_gt, h_min⟩
  have h_prev : T.u i (cellEntry T i r hr_ge hr_lt).castSucc + (i.val : ℤ) ≤ (r : ℤ) := by
    rcases Nat.eq_zero_or_pos (cellEntry T i r hr_ge hr_lt).val with ht0 | ht_pos
    · have h_eq0 : (cellEntry T i r hr_ge hr_lt).castSucc = 0 := by
        apply Fin.ext
        exact ht0
      rw [h_eq0, T.start_eq i]
      omega
    · let t' : Fin N := ⟨(cellEntry T i r hr_ge hr_lt).val - 1, by omega⟩
      have h_lt : t' < cellEntry T i r hr_ge hr_lt := by
        change (cellEntry T i r hr_ge hr_lt).val - 1 < (cellEntry T i r hr_ge hr_lt).val
        omega
      have h_not := h_min t' h_lt
      have h_succ_eq : t'.succ = (cellEntry T i r hr_ge hr_lt).castSucc := by
        apply Fin.ext
        change (cellEntry T i r hr_ge hr_lt).val - 1 + 1 = (cellEntry T i r hr_ge hr_lt).val
        omega
      rw [h_succ_eq] at h_not
      omega
  rcases T.step_valid i (cellEntry T i r hr_ge hr_lt) with h0 | h1 <;> omega

/-- **定理（桥 B2 列严格性）**：`cellEntry` 在每一列上关于行标 `r` 严格递增 -/
theorem cellEntry_col_strict {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν)
    (i : Fin m) (r₁ r₂ : ℕ) (hr₁ : ν i ≤ r₁) (h_lt : r₁ < r₂) (hr₂ : r₂ < μ i) :
    cellEntry T i r₁ hr₁ (lt_trans h_lt hr₂) <
    cellEntry T i r₂ (le_trans hr₁ (le_of_lt h_lt)) hr₂ := by
  have h_val1 := cellEntry_exact_val T i r₁ hr₁ (lt_trans h_lt hr₂)
  have h_val2 := cellEntry_exact_val T i r₂ (le_trans hr₁ (le_of_lt h_lt)) hr₂
  have h_ne :
      cellEntry T i r₁ hr₁ (lt_trans h_lt hr₂) ≠
      cellEntry T i r₂ (le_trans hr₁ (le_of_lt h_lt)) hr₂ := by
    intro h_eq
    rw [h_eq] at h_val1
    omega
  have h_not_lt :
      ¬(cellEntry T i r₂ (le_trans hr₁ (le_of_lt h_lt)) hr₂ <
        cellEntry T i r₁ hr₁ (lt_trans h_lt hr₂)) := by
    intro h_lt_t
    have h_min1 := (cellEntry_spec T i r₁ hr₁ (lt_trans h_lt hr₂)).2
      (cellEntry T i r₂ (le_trans hr₁ (le_of_lt h_lt)) hr₂) h_lt_t
    omega
  rcases lt_trichotomy
    (cellEntry T i r₁ hr₁ (lt_trans h_lt hr₂))
    (cellEntry T i r₂ (le_trans hr₁ (le_of_lt h_lt)) hr₂) with hlt | heq | hgt
  · exact hlt
  · exact absurd heq h_ne
  · exact absurd hgt h_not_lt

/-- 严格递减整数序列加上下标后单调不增：`i ≤ j → f j + j ≤ f i + i` -/
lemma add_val_le_of_strictAnti_aux {m : ℕ} (f : Fin m → ℤ)
    (hf : ∀ i j : Fin m, i < j → f j < f i) :
    ∀ (d : ℕ) (i j : Fin m), j.val = i.val + d →
      f j + (j.val : ℤ) ≤ f i + (i.val : ℤ)
  | 0, i, j, hd => by
    have hij : i = j := by
      apply Fin.ext
      omega
    subst hij
    omega
  | d + 1, i, j, hd => by
    have hm : i.val + d < m := by
      have := j.isLt
      omega
    let k : Fin m := ⟨i.val + d, hm⟩
    have h_ih := add_val_le_of_strictAnti_aux f hf d i k rfl
    have h_kj : k < j := by
      change i.val + d < j.val
      omega
    have h_step : f j < f k := hf k j h_kj
    change f k + ((i.val + d : ℕ) : ℤ) ≤ f i + (i.val : ℤ) at h_ih
    omega

/-- **定理（桥 B2 行弱递增性）**：`cellEntry` 在同一行 `r` 上关于列标 `i ≤ j` 弱递增 -/
theorem cellEntry_row_weak {m N : ℕ} {μ ν : Fin m → ℕ} (T : SkewSSYT m N μ ν)
    (i j : Fin m) (hij : i ≤ j) (r : ℕ)
    (hri_ge : ν i ≤ r) (hri_lt : r < μ i)
    (hrj_ge : ν j ≤ r) (hrj_lt : r < μ j) :
    cellEntry T i r hri_ge hri_lt ≤ cellEntry T j r hrj_ge hrj_lt := by
  have hj_gt : (r : ℤ) < T.u j (cellEntry T j r hrj_ge hrj_lt).succ + (j.val : ℤ) :=
    (cellEntry_spec T j r hrj_ge hrj_lt).1
  have h_col_le :
      T.u j (cellEntry T j r hrj_ge hrj_lt).succ + (j.val : ℤ) ≤
      T.u i (cellEntry T j r hrj_ge hrj_lt).succ + (i.val : ℤ) :=
    add_val_le_of_strictAnti_aux
      (fun k => T.u k (cellEntry T j r hrj_ge hrj_lt).succ)
      (T.row_weak (cellEntry T j r hrj_ge hrj_lt).succ)
      (j.val - i.val) i j
      (by have : i.val ≤ j.val := hij; omega)
  have hi_gt : (r : ℤ) < T.u i (cellEntry T j r hrj_ge hrj_lt).succ + (i.val : ℤ) := by
    omega
  by_contra h_not_le
  have h_lt : cellEntry T j r hrj_ge hrj_lt < cellEntry T i r hri_ge hri_lt :=
    not_le.mp h_not_le
  exact (cellEntry_spec T i r hri_ge hri_lt).2 (cellEntry T j r hrj_ge hrj_lt) h_lt hi_gt

/-- **第二 Jacobi–Trudi 恒等式（斜分拆一般形式，Nägelsbach–Kostka 恒等式）**：
    `det (e_{μ_i - ν_j - i + j}(x))_{0 ≤ i, j < m} = s_{λ/ν}(x)` -/
theorem second_jacobi_trudi_skew {m N : ℕ} {μ ν : Fin m → ℕ}
    (hμ : Antitone μ) (hν : Antitone ν) (x : Fin N → R) :
    (jacobiTrudiMatrix μ ν x).det = skewSchurPoly μ ν x := by
  rw [det_jacobiTrudiMatrix_eq_sum_pathConfig μ ν x]
  rw [gv_cancellation_complete hμ hν x Finset.univ (fun _ _ => Finset.mem_univ _)]
  exact sum_nonIntersecting_eq_skewSchurPoly hμ hν x

/-- **第二 Jacobi–Trudi 恒等式（普通分拆特例 `ν = 0`）**：
    `det (e_{μ_i - i + j}(x))_{0 ≤ i, j < m} = s_λ(x)` -/
theorem second_jacobi_trudi {m N : ℕ} {μ : Fin m → ℕ} (hμ : Antitone μ) (x : Fin N → R) :
    (jacobiTrudiMatrix μ (fun _ => 0) x).det = skewSchurPoly μ (fun _ => 0) x :=
  second_jacobi_trudi_skew hμ (fun _ _ _ => le_refl 0) x

end
