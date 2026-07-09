;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "add"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("amsmath" "") ("fullpage" "")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "amsmath"
    "fullpage")
   (TeX-add-symbols
    '("quot" 1)
    "mlq"
    "mrq"))
 :latex)

