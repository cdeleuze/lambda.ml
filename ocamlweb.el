(require 'mmm-mode)

(setq mmm-submode-decoration-level 0)

(mmm-add-classes
 '((ocamlweb
    :submode LaTeX-mode
    :face mmm-default-submode-face
    :front "(\\*[psi]?\n?"  ;; peut être pas les (*i  i*) ?
    :back "i?\\*)")
   ))

(mmm-mode)
(mmm-ify-by-class 'ocamlweb)
