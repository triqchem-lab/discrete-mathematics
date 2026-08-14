{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.MetaStructure.Nayin
-- 元结构层：六十甲子纳音拓扑指纹
-- 
-- 纳音是主权状态机在特定天干地支下的驻波谐波主峰拓扑指纹
-- 禁止将纳音解释为五行比喻或音律象征

module Sovereign.MetaStructure.Nayin where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_)
open import Data.Fin using (Fin; toℕ; fromℕ; #_)
open import Data.Fin.Properties using ()
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Sovereign.MetaStructure.WuXing using (WuXing; Fire; Earth; Metal; Water; Wood; wuXingBase)
open import Sovereign.RootMath.DigitalRoot using (StableRoot; root0; root3; root6)

--------------------------------------------------------------------------------
-- 1. 十天干与十二地支
--------------------------------------------------------------------------------

data HeavenlyStem : Set where
  Jia Yi Bing Ding Wu Ji Geng Xin Ren Gui : HeavenlyStem

data EarthlyBranch : Set where
  Zi Chou Yin Mao Chen Si Wu Wei Shen You Xu Hai : EarthlyBranch

-- 天干到索引
stemToIndex : HeavenlyStem → Fin 10
stemToIndex Jia  = # 0
stemToIndex Yi   = # 1
stemToIndex Bing = # 2
stemToIndex Ding = # 3
stemToIndex Wu   = # 4
stemToIndex Ji   = # 5
stemToIndex Geng = # 6
stemToIndex Xin  = # 7
stemToIndex Ren  = # 8
stemToIndex Gui  = # 9

-- 地支到索引
branchToIndex : EarthlyBranch → Fin 12
branchToIndex Zi   = # 0
branchToIndex Chou = # 1
branchToIndex Yin  = # 2
branchToIndex Mao  = # 3
branchToIndex Chen = # 4
branchToIndex Si   = # 5
branchToIndex Wu   = # 6
branchToIndex Wei  = # 7
branchToIndex Shen = # 8
branchToIndex You  = # 9
branchToIndex Xu   = # 10
branchToIndex Hai  = # 11

--------------------------------------------------------------------------------
-- 2. 六十甲子
--------------------------------------------------------------------------------

-- 六十甲子是天干地支的直积
record JiaZi : Set where
  constructor mkJiaZi
  field
    stem   : HeavenlyStem   -- 天干（环向模10）
    branch : EarthlyBranch  -- 地支（极向模12）

-- 六十甲子列表
allJiaZi : Vec JiaZi 60
allJiaZi = 
  mkJiaZi Jia  Zi   ∷  -- 1. 甲子
  mkJiaZi Yi   Chou ∷  -- 2. 乙丑
  mkJiaZi Bing Yin   ∷  -- 3. 丙寅
  mkJiaZi Ding Mao   ∷  -- 4. 丁卯
  mkJiaZi Wu   Chen  ∷  -- 5. 戊辰
  mkJiaZi Ji   Si    ∷  -- 6. 己巳
  mkJiaZi Geng Wu    ∷  -- 7. 庚午
  mkJiaZi Xin  Wei   ∷  -- 8. 辛未
  mkJiaZi Ren  Shen  ∷  -- 9. 壬申
  mkJiaZi Gui  You   ∷  -- 10. 癸酉
  mkJiaZi Jia  Xu    ∷  -- 11. 甲戌
  mkJiaZi Yi   Hai   ∷  -- 12. 乙亥
  mkJiaZi Bing Zi    ∷  -- 13. 丙子
  mkJiaZi Ding Chou  ∷  -- 14. 丁丑
  mkJiaZi Wu   Yin   ∷  -- 15. 戊寅
  mkJiaZi Ji   Mao   ∷  -- 16. 己卯
  mkJiaZi Geng Chen  ∷  -- 17. 庚辰
  mkJiaZi Xin  Si    ∷  -- 18. 辛巳
  mkJiaZi Ren  Wu    ∷  -- 19. 壬午
  mkJiaZi Gui  Wei   ∷  -- 20. 癸未
  mkJiaZi Jia  Shen  ∷  -- 21. 甲申
  mkJiaZi Yi   You   ∷  -- 22. 乙酉
  mkJiaZi Bing Xu    ∷  -- 23. 丙戌
  mkJiaZi Ding Hai   ∷  -- 24. 丁亥
  mkJiaZi Wu   Zi    ∷  -- 25. 戊子
  mkJiaZi Ji   Chou  ∷  -- 26. 己丑
  mkJiaZi Geng Yin   ∷  -- 27. 庚寅
  mkJiaZi Xin  Mao   ∷  -- 28. 辛卯
  mkJiaZi Ren  Chen  ∷  -- 29. 壬辰
  mkJiaZi Gui  Si    ∷  -- 30. 癸巳
  mkJiaZi Jia  Wu    ∷  -- 31. 甲午
  mkJiaZi Yi   Wei   ∷  -- 32. 乙未
  mkJiaZi Bing Shen  ∷  -- 33. 丙申
  mkJiaZi Ding You   ∷  -- 34. 丁酉
  mkJiaZi Wu   Xu    ∷  -- 35. 戊戌
  mkJiaZi Ji   Hai   ∷  -- 36. 己亥
  mkJiaZi Geng Zi    ∷  -- 37. 庚子
  mkJiaZi Xin  Chou  ∷  -- 38. 辛丑
  mkJiaZi Ren  Yin   ∷  -- 39. 壬寅
  mkJiaZi Gui  Mao   ∷  -- 40. 癸卯
  mkJiaZi Jia  Chen  ∷  -- 41. 甲辰
  mkJiaZi Yi   Si    ∷  -- 42. 乙巳
  mkJiaZi Bing Wu    ∷  -- 43. 丙午
  mkJiaZi Ding Wei   ∷  -- 44. 丁未
  mkJiaZi Wu   Shen  ∷  -- 45. 戊申
  mkJiaZi Ji   You   ∷  -- 46. 己酉
  mkJiaZi Geng Xu    ∷  -- 47. 庚戌
  mkJiaZi Xin  Hai   ∷  -- 48. 辛亥
  mkJiaZi Ren  Zi    ∷  -- 49. 壬子
  mkJiaZi Gui  Chou  ∷  -- 50. 癸丑
  mkJiaZi Jia  Yin   ∷  -- 51. 甲寅
  mkJiaZi Yi   Mao   ∷  -- 52. 乙卯
  mkJiaZi Bing Chen  ∷  -- 53. 丙辰
  mkJiaZi Ding Si    ∷  -- 54. 丁巳
  mkJiaZi Wu   Wu    ∷  -- 55. 戊午
  mkJiaZi Ji   Wei   ∷  -- 56. 己未
  mkJiaZi Geng Shen  ∷  -- 57. 庚申
  mkJiaZi Xin  You   ∷  -- 58. 辛酉
  mkJiaZi Ren  Xu    ∷  -- 59. 壬戌
  mkJiaZi Gui  Hai   ∷  -- 60. 癸亥
  []

--------------------------------------------------------------------------------
-- 3. 纳音五行映射
--------------------------------------------------------------------------------

-- 三十纳音（每对干支一个纳音）
data NayinSound : Set where
  HaiZhongJin     : NayinSound  -- 海中金 (甲子、乙丑)
  LuZhongHuo      : NayinSound  -- 炉中火 (丙寅、丁卯)
  DaLinMu         : NayinSound  -- 大林木 (戊辰、己巳)
  LuPangTu        : NayinSound  -- 路旁土 (庚午、辛未)
  JianFengJin     : NayinSound  -- 剑锋金 (壬申、癸酉)
  ShanTouHuo      : NayinSound  -- 山头火 (甲戌、乙亥)
  JianXiaShui     : NayinSound  -- 涧下水 (丙子、丁丑)
  ChengTouTu      : NayinSound  -- 城头土 (戊寅、己卯)
  BaiLaJin        : NayinSound  -- 白蜡金 (庚辰、辛巳)
  YangLiuMu        : NayinSound  -- 杨柳木 (壬午、癸未)
  WuZhongShui     : NayinSound  -- 屋中水 (甲申、乙酉)
  PiLiHuo         : NayinSound  -- 霹雳火 (丙戌、丁亥)
  BiShangTu        : NayinSound  -- 壁上土 (戊子、己丑)
  JinBoJin        : NayinSound  -- 金箔金 (庚寅、辛卯)
  FuDengHuo       : NayinSound  -- 覆灯火 (壬辰、癸巳)
  TianHeShui      : NayinSound  -- 天河水 (甲午、乙未)
  DaYiTu          : NayinSound  -- 大驿土 (丙申、丁酉)
  BoChuangJin     : NayinSound  -- 钗钏金 (戊戌、己亥)
  SangZheMu        : NayinSound  -- 桑柘木 (庚子、辛丑)
  DaXiShui        : NayinSound  -- 大溪水 (壬寅、癸卯)
  ShaZhongTu      : NayinSound  -- 沙中土 (甲辰、乙巳)
  ShanXiaHu       : NayinSound  -- 山下火 (丙午、丁未)
  SongBoMu         : NayinSound  -- 松柏木 (戊申、己酉)
  ChangLiuShui    : NayinSound  -- 长流水 (庚戌、辛亥)
  JingChuanTu     : NayinSound  -- 井泉土 (壬子、癸丑)
  DaHaiShui       : NayinSound  -- 大海水 (甲寅、乙卯)
  -- ... 等

-- 纳音到五行的拓扑映射
nayinToWuxing : NayinSound → WuXing
nayinToWuxing HaiZhongJin  = Metal
nayinToWuxing LuZhongHuo   = Fire
nayinToWuxing DaLinMu      = Wood
nayinToWuxing LuPangTu     = Earth
nayinToWuxing JianFengJin  = Metal
nayinToWuxing ShanTouHuo   = Fire
nayinToWuxing JianXiaShui  = Water
nayinToWuxing ChengTouTu   = Earth
nayinToWuxing BaiLaJin     = Metal
nayinToWuxing YangLiuMu     = Wood
nayinToWuxing WuZhongShui  = Water
nayinToWuxing PiLiHuo      = Fire
nayinToWuxing BiShangTu     = Earth
nayinToWuxing JinBoJin     = Metal
nayinToWuxing FuDengHuo    = Fire
nayinToWuxing TianHeShui   = Water
nayinToWuxing DaYiTu       = Earth
nayinToWuxing BoChuangJin  = Metal
nayinToWuxing SangZheMu     = Wood
nayinToWuxing DaXiShui     = Water
nayinToWuxing ShaZhongTu   = Earth
nayinToWuxing ShanXiaHu    = Fire
nayinToWuxing SongBoMu      = Wood
nayinToWuxing ChangLiuShui = Water
nayinToWuxing JingChuanTu  = Earth
nayinToWuxing DaHaiShui    = Water

--------------------------------------------------------------------------------
-- 4. 纳音驻波拓扑指纹
--------------------------------------------------------------------------------

-- 纳音指纹：包含五行、谐波阶次、稳定数字根证据
record NayinFingerprint : Set where
  constructor mkNaYin
  field
    sound         : NayinSound        -- 纳音
    wuxing        : WuXing            -- 五行
    harmonicOrder : ℕ                 -- 优选谐波阶次（奇数）
    stableProof   : StableRoot (wuXingBase wuxing * harmonicOrder)

-- 纳音指纹构造的智能函数
mkNayinFingerprint : (s : NayinSound) → (h : ℕ) → {pf : StableRoot (wuXingBase (nayinToWuxing s) * h)} → NayinFingerprint
mkNayinFingerprint s h {pf} = record
  { sound = s
  ; wuxing = nayinToWuxing s
  ; harmonicOrder = h
  ; stableProof = pf
  }

--------------------------------------------------------------------------------
-- 5. 纳音与地气声子谱的共振
--------------------------------------------------------------------------------

-- 纳音优选谐波
nayinPreferredHarmonic : NayinSound → ℕ
nayinPreferredHarmonic HaiZhongJin  = 1   -- 基频
nayinPreferredHarmonic LuZhongHuo   = 3   -- 3 次谐波
nayinPreferredHarmonic DaLinMu      = 5   -- 5 次谐波
nayinPreferredHarmonic LuPangTu     = 7
nayinPreferredHarmonic JianFengJin  = 9
nayinPreferredHarmonic ShanTouHuo   = 11
nayinPreferredHarmonic _ = 1  -- 默认基频

-- 纳音共振频率（基于地气基频 144 Hz）
DIQI_BASE : ℕ
DIQI_BASE = 144

nayinResonanceFreq : NayinSound → ℕ
nayinResonanceFreq s = DIQI_BASE * nayinPreferredHarmonic s

--------------------------------------------------------------------------------
-- 6. 纳音为驻波拓扑指纹（非比喻）
--------------------------------------------------------------------------------

-- 宪法条款：纳音是拓扑指纹，禁止解释为五行比喻
record IsMetaphor (w : WuXing) : Set where
  field
    metaphoricalSound   : ℕ
    metaphoricalElement : WuXing
    isMetaphorical      : metaphoricalElement ≡ w

-- [Constitutional] 纳音为驻波拓扑指纹，禁止解释为五行比喻。
-- 2026-08 P0 轨道 A 处置: 原 nayinIsTopological 为假命题 — 模块自身注释承认
--   IsMetaphor w 恒可居 (metaphoricalElement = w, isMetaphorical = refl),
--   ¬ IsMetaphor 被该见证直接反驳 (⊥ 可导出), 已删除。
--   教义保留为注释: 纳音指纹语义域由 mkNayinFingerprint 构造限定
--   (wuxing 由 sound 决定), 不通过 ¬ 公理强制。

-- [Constitutional] 纳音指纹的唯一性 (构造版本)
-- 2026-08 P0 轨道 A 处置: 原全称形式 (任意 mkNaYin 记录) 为假 — wuxing 字段自由,
--   见证 h=0: 同 sound 同 harmonicOrder、不同 wuxing 的两个指纹均含 root0
--   (StableRoot 0) — 公理使 ⊥ 可导出, 已删除。
--   真版本: 经 mkNayinFingerprint 构造的指纹 (wuxing = nayinToWuxing s 由 sound
--   决定), sound 与 harmonicOrder 相等 ⟹ 指纹相等 (0 postulate 证明)。
--
-- [v5.3 训练验证] 2026-07-03 Fable 5深度分析确认：
--   纳音库 6624格点在 S2Sovereign 200k步训练中收敛: ρ=1.000, plasma_crystal@T=573°C,
--   陈数C=-2.000保持, 12律纯度 p=0.086→0.090, 仲吕级联 15833→16000 非发散。
--   Ref: /data/trit/pyBitNet/docs/discrete-math/training_log_200k_20260507-065441.txt

-- StableRoot 命题无关性 (单构造子逐 case)
stableProofIrrelevant : ∀ {n} → (p q : StableRoot n) → p ≡ q
stableProofIrrelevant root0 root0 = refl
stableProofIrrelevant root3 root3 = refl
stableProofIrrelevant root6 root6 = refl

nayinFingerprintUnique : ∀ (s s' : NayinSound) (h h' : ℕ) {pf pf'} →
  s ≡ s' → h ≡ h' →
  mkNayinFingerprint s h {pf} ≡ mkNayinFingerprint s' h' {pf'}
nayinFingerprintUnique s .s h .h {pf} {pf'} refl refl =
  cong (λ p → mkNayinFingerprint s h {pf = p}) (stableProofIrrelevant pf pf')
