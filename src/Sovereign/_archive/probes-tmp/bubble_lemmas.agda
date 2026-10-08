bubble1 : v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9))))))))
bubble1 = cong (v1 +_) (cong (v2 +_) (swap3 v3 v4 (v5 + (v6 + (v7 + (v8 + (v9)))))))

bubble2 : v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9))))))))
bubble2 = cong (v1 +_) (swap3 v2 v4 (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))

bubble3 : v1 + (v4 + (v2 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v5 + (v7 + (v6 + (v8 + (v9))))))))
bubble3 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (cong (v3 +_) (cong (v5 +_) (swap3 v6 v7 (v8 + (v9)))))))

bubble4 : v1 + (v4 + (v2 + (v3 + (v5 + (v7 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v7 + (v5 + (v6 + (v8 + (v9))))))))
bubble4 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (cong (v3 +_) (swap3 v5 v7 (v6 + (v8 + (v9)))))))

bubble5 : v1 + (v4 + (v2 + (v3 + (v7 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v7 + (v3 + (v5 + (v6 + (v8 + (v9))))))))
bubble5 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (swap3 v3 v7 (v5 + (v6 + (v8 + (v9)))))))

bubble6 : v1 + (v4 + (v2 + (v7 + (v3 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v3 + (v5 + (v6 + (v8 + (v9))))))))
bubble6 = cong (v1 +_) (cong (v4 +_) (swap3 v2 v7 (v3 + (v5 + (v6 + (v8 + (v9)))))))

bubble7 : v1 + (v4 + (v7 + (v2 + (v3 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v6 + (v8 + (v9))))))))
bubble7 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (swap3 v3 v5 (v6 + (v8 + (v9)))))))

bubble8 : v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v8 + (v6 + (v9))))))))
bubble8 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (cong (v5 +_) (cong (v3 +_) (swap3 v6 v8 (v9)))))))

bubble9 : v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v8 + (v6 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v8 + (v3 + (v6 + (v9))))))))
bubble9 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (cong (v5 +_) (swap3 v3 v8 (v6 + (v9)))))))
