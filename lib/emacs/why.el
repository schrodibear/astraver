
;; why.el - GNU Emacs mode for Why
;; Copyright (C) 2002 Jean-Christophe FILLIATRE

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
  "grab the next non-empt proof below and insert it"
  (interactive)
  (if (save-excursion (why-go-and-get-next-proof)) (yank)))



    