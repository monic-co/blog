(enforce-pact-version "2.4.1")

(define-keyset 'accounts-admin-keyset
  (read-keyset "accounts-admin-keyset"))

(module accounts 'accounts-admin-keyset
  "Demo module"

  (defschema account
    (meta "account"
      (invariant (>= balance 0)))
    balance:integer
    ks:keyset)
  (deftable accounts:{account})

(defun transfer (from:string to:string amount:integer)
  (meta "Transfer money between accounts"
    (properties [
      (row-enforced 'accounts 'ks from)
      (= (column-delta 'accounts 'balance) 0)
      ]))

  (with-read accounts from { 'balance := from-bal, 'ks := from-ks }
    (with-read accounts to { 'balance := to-bal }
      (enforce-keyset from-ks)
      (enforce (>= from-bal amount) "Insufficient Funds")
      (enforce (> amount 0)         "Amount must be positive")
      (enforce (!= from to)         "Sender and recipient can't be the same")
      (update accounts from { "balance": (- from-bal amount) })
      (update accounts to   { "balance": (+ to-bal amount) })))))
