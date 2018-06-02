(enforce-pact-version "2.3")
(define-keyset 'accounts-admin-keyset
  (read-keyset "accounts-admin-keyset"))

(module accounts 'accounts-admin-keyset
  "Demo module"
  (defschema account
    ("account"
      (invariants [(>= balance 0)]))
    balance:integer
    ks:keyset)
  (deftable accounts:{account})

  (defun transfer (from:string to:string amount:integer)
    ("Transfer money between accounts"
      (properties [
        (row-enforced accounts 'ks from)
        (column-conserves accounts 'balance)
        ]))
    (let ((from-bal (at 'balance (read accounts from)))
          (from-ks  (at 'ks      (read accounts from)))
          (to-bal   (at 'balance (read accounts to))))
      (enforce-keyset from-ks)
      (enforce (>= from-bal amount) "Insufficient Funds")
      (enforce (> amount 0)         "Amount must be positive")
      (update accounts from { "balance": (- from-bal amount) })
      (update accounts to   { "balance": (+ to-bal amount) }))))
