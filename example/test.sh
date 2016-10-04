(go run calc.go <<EOF
SetLogging[True]
bar[1, foo[a, b]] + bar[5, foo[a, b]] /. bar[amatch_Integer, foo[cmatch__]] -> amatch*buzz[cmatch]
EOF
) 2>&1
#) 2>&1 | head -n 50
