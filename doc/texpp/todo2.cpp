\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\verb|#|pragma~FloatModel(strict)~\\
\verb|#|pragma~FloatModel(full)~\\
\verb|#|pragma~JessieFloatRoundingMode(downward)~\\
\verb|#|pragma~JessieFloatRoundingMode(...)~\\
~\\
Rémonter~tous~les~prédicats~au~langage~ACSL~:~~\\
~\\
~~\begin{slshape}\rmfamily\color{darkgreen}//~5~modes~d'arrondi\end{slshape}~\\
Nearest\_{}even,To\_{}zero,Round\_{}up,Round\_{}down,Nearest\_{}away~\\
~\\
~~\begin{slshape}\rmfamily\color{darkgreen}//~Casting~\end{slshape}~\\
\textbf{logic}~float~float\_{}of\_{}real(rounding\_{}mode~m,real~x);~\\
\textbf{logic}~double~double\_{}of\_{}real(rounding\_{}mode~m,real~x);~\\
~\\
\end{flushleft}