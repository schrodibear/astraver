
;; why.el - GNU Emacs mode for Why
;; Copyright (C) 2002 Jean-Christophe FILLIATRE

(defvar why-mode-hook nil)
(defvar why-mode-map nil
  "Keymap for Why major mode")

(if why-mode-map nil
  (setq why-mode-map (make-keymap)))

(setq auto-mode-alist
      (append
       '(("\\.mlw" . why-mode))
       auto-mode-alist))

;; font-lock

(defun why-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst why-font-lock-keywords-1
  (list
   '("{\\([^}]*\\)}" . font-lock-type-face)
   '("(\\*\\([^*]\\|\\*[^)]\\)*\\*)" . font-lock-comment-face)
   `(,(why-regexp-opt '("external" "logic" "parameter" "exception")) . font-lock-builtin-face)
   `(,(why-regexp-opt '("let" "rec" "in" "if" "then" "else" "begin" "end" "while" "do" "done" "label" "assert")) . font-lock-keyword-face)
   ; `(,(why-regexp-opt '("unit" "bool" "int" "float" "prop" "array")) . font-lock-type-face)
   )
  "Minimal highlighting for Why mode")

(defvar why-font-lock-keywords why-font-lock-keywords-1
  "Default highlighting for Why mode")

;; syntax

(defvar why-mode-syntax-table nil
  "Syntax table for why-mode")

(defun why-create-syntax-table ()
  (if why-mode-syntax-table
      ()
    (setq why-mode-syntax-table (make-syntax-table))
    (set-syntax-table why-mode-syntax-table)
    (modify-syntax-entry ?_ "w" why-mode-syntax-table)))

;; utility functions 

(defun why-go-and-get-next-proof ()
  (let ((bp (search-forward "Proof." nil t)))
    (if (null bp) (progn (message "Cannot find a proof below") nil)
      (let ((bs (re-search-forward "Save\\|Qed\\." nil t)))
	(if (null bs) (progn (message "Cannot find a proof below") nil)
	  (if (> bs (+ bp 6))
	      (let ((br (+ bp 1))
		    (er (progn (goto-char bs) (beginning-of-line) (point))))
		(progn (kill-region br er) t))
	    (why-go-and-get-next-proof)))))))

(defun why-grab-next-proof ()
  "grab the next non-empty proof below and insert it at current point"
  (interactive)
  (if (save-excursion (why-go-and-get-next-proof)) (yank)))

;; setting the mode

(defun why-mode ()
  "Major mode for editing Why programs"
  (interactive)
  (kill-all-local-variables)
  (why-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(why-font-lock-keywords))
  ; indentation
  ; (make-local-variable 'indent-line-function)
  ; (setq indent-line-function 'why-indent-line)
  ; providing the mode
  (setq major-mode 'why-mode)
  (setq mode-name "WHY")
  (run-hooks 'why-mode-hook))

(provide 'why-mode)

