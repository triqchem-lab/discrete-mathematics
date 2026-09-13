module T3 where
data T3 : Set where t0 t1 t2 : T3
step : T3 → T3
step t0 = t1
step t1 = t2
step t2 = t0
