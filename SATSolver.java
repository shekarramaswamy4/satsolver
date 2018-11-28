import java.io.*;
import java.util.*;

public class SATSolver {

  /**
   * A formula is a set of clauses. This class has typical methods of
   * a set, such as getters, adders, etc.
   */
  private class Formula {
    private Set<Clause> formula;

    public Formula(Set<Clause> formula) {
      this.formula = formula;
    }

    public void addToFormula(Clause c) {
      formula.add(c);
    }

    public Set<Clause> getFormula() {
      return formula;
    }

    public Set<Integer> getVars() {
      Set<Integer> s = new HashSet<>();
      for (Clause c : formula) {
        s.addAll(c.getVars());
      }
      return s;
    }

    public Set<Literal> getLiterals() {
      Set<Literal> l = new HashSet<>();
      for (Clause c : formula) {
        l.addAll(c.getLiterals());
      }
      return l;
    }
  }

  /**
   * A clause is a set of literals.
   */
  private class Clause  {
    private Set<Literal> literals;

    public Clause(Set<Literal> l) {
      this.literals = l;
    }

    public void addToSet(Literal l) {
      literals.add(l);
    }

    public Set<Literal> getLiterals() {
      return literals;
    }

    public Set<Integer> getVars() {
      Set<Integer> s = new HashSet<>();
      for (Literal l : literals) {
        s.add(Integer.valueOf(l.getVal()));
      }
      return s;
    }
  }

  /**
   * A literal is a single variable, represented by an Integer and its
   * corresponding sign (true = positive, false = negative).
   */
  private class Literal {
    private boolean sign;
    private Integer val;

    public Literal(boolean s, Integer v) {
      this.sign = s;
      this.val = v;
    }

    public boolean getSign() {
      return sign;
    }

    public void setSign(boolean sign) {
      this.sign = sign;
    }

    public Integer getVal() {
      return val;
    }

    public void setVal(int val) {
      this.val = val;
    }

    public boolean equals(Literal l) {
      if (l.getSign() == this.sign &&
              l.getVal().compareTo(val) == 0) {
        return true;
      }
      return false;
    }

    public boolean sameValDifSign(Literal l) {
      if (l.getSign() != this.sign &&
              l.getVal().compareTo(val) == 0) {
        return true;
      }
      return false;
    }

    public boolean equalToAny(Set<Literal> l) {
      for (Literal cur : l) {
        if (this.equals(cur)) {
          return true;
        }
      }
      return false;
    }

    public boolean equalToAnyOppositeSign(Set<Literal> l) {
      for (Literal cur : l) {
        if (this.sign != cur.getSign() &&
                this.val.compareTo(cur.getVal()) == 0) {
          return true;
        }
      }
      return false;
    }
  }

  /*SAT SOLVER CLASS STARTS HERE*/

  public SATSolver() {
  }

  /**
   * Creates a new formula
   */
  public Formula createFormula() {
    return new Formula(new HashSet<>());
  }

  /**
   * Creates a new clause
   */
  public Clause createClause() {
    return new Clause(new HashSet<>());
  }

  /**
   * Creates a new literal with sign sign and value num
   */
  private Literal createLiteral(boolean sign, String num) {
    boolean pos;
    if (sign) {
      pos = true;
    } else {
      pos = false;
    }

    Integer var = Integer.parseInt(num);
    return new Literal(pos, var);
  }

  /**
   * Solves the inputted formula, recursively using DPLL method
   */
  public Map<Integer, Boolean> solve(Formula f) {

    Set<Literal> recurVars = f.getLiterals();
    f = DPLL(recurVars, f);

    Map<Integer, Boolean> valMap = new HashMap<>();

    if (f == null) {
      return null;
    } else {
      for (Clause c : f.getFormula()) {
        for (Literal l : c.getLiterals()) {
          valMap.put(l.getVal(), l.getSign());
        }
      }
    }
    return valMap;
  }

  /**
   * Implementation of DPLL algorithm.
   */
  private Formula DPLL(Set<Literal> vars,
                       Formula f) {

    f = unitProp(f);
    f = pureElim(f);

    if (checkForEmpty(f)) {
      return null; //for unsat
    }

    int checkF = checkFormula(vars, f);
    if (checkF == 2) {
      return null; //for unsat
    }
    if (checkF == 1) {
      return f;
    }

    Literal x = findNextLiteral(vars, f);

    Formula tempFPos = createFormulaFromF(f);
    Clause posClause = new Clause(new HashSet<>());
    posClause.addToSet(new Literal(true, x.getVal()));
    tempFPos.addToFormula(posClause);

    Formula tempFNeg = createFormulaFromF(f);
    Clause negClause = new Clause(new HashSet<>());
    negClause.addToSet(new Literal(false, x.getVal()));
    tempFNeg.addToFormula(negClause);

    Formula fPos = DPLL(vars, tempFPos);
    if (fPos != null && !checkForEmpty(fPos)) {
      return fPos;
    } else {
      return DPLL(vars, tempFNeg);
    }
  }

  /**
   * Finds the next literal to look at.
   */
  private Literal findNextLiteral(Set<Literal> vars, Formula f) {
    for (Clause c : f.getFormula()) {
      if (c.getLiterals().size() > 1) {
        for (Literal l : c.getLiterals()) {
          if (l.equalToAny(vars)) {
            return l;
          }
        }
      }
    }
    for (Literal l : vars) {
      boolean foundLit = false;
      for (Clause c : f.getFormula()) {
        if (c.getLiterals().size() == 1) {
          for (Literal cur : c.getLiterals()) {
            if (l.getVal().compareTo(cur.getVal()) == 0) {
              foundLit = true;
            }
          }
        }
      }
      if (!foundLit) {
        return l;
      }
    }
    return null; //should never get here
  }

  /**
   * Creates a duplicate formula of f
   */
  private Formula createFormulaFromF(Formula f) {
    Formula reconstructed = new Formula(new HashSet<>());
    for (Clause c : f.getFormula()) {
      reconstructed.addToFormula(c);
    }
    return reconstructed;
  }

  /**
   * Returns true if empty clause is in f.
   */
  private boolean checkForEmpty(Formula f) {
    for (Clause c : f.getFormula()) {
      if (c.getLiterals().size() == 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether formula is all unit clauses / has all vars / is satisfiable
   * 0 is keep checking, 1 is sat, 2 is unsat
   */
  private int checkFormula(Set<Literal> vars, Formula f) {
    for (Literal l : vars) {
      boolean foundL = false;
      boolean foundPos = false;
      boolean foundNeg = false;
      for (Clause c : f.getFormula()) {
        if (c.getLiterals().size() == 1) {
          for (Literal cur : c.getLiterals()) {
            if (l.getVal().compareTo(cur.getVal()) == 0) {
              foundL = true;

              if (cur.getSign() == true) {
                foundPos = true;
              } else {
                foundNeg = true;
              }

            }
          }
        } else {
          return 0;
        }
      }
      if (foundL != true) {
        return 0;
      }

      if (!((foundPos || foundNeg) && !(foundPos && foundNeg))) {
        //unsatisfiable
        return 2;
      }
    }
    return 1;
  }

  /**
   * Pure Elimination cleaning of a formula
   */
  private Formula pureElim(Formula f) {
    Formula reconstructed = new Formula(new HashSet<>());
    Set<Literal> lits = pureLiterals(f);
    for (Clause c : f.getFormula()) {
      boolean shouldAddClause = true;
      for (Literal cur : c.getLiterals()) {
        if (cur.equalToAny(lits)) {
          shouldAddClause = false;
        }
      }
      if (shouldAddClause) {
        reconstructed.addToFormula(c);
      }
    }
    for (Literal l : lits) {
      Clause c = new Clause(new HashSet<>());
      c.addToSet(l);
      reconstructed.addToFormula(c);
    }
    return reconstructed;
  }

  /**
   * Unit propagation cleaning
   */
  private Formula unitProp(Formula f) {
    Formula reconstructed = new Formula(new HashSet<>());
    Set<Literal> literals = unitClauses(f);
    for (Clause c : f.getFormula()) {
      if (c.getLiterals().size() > 1) {
        boolean shouldAddClause = true;
        Clause newClause = new Clause(new HashSet<>());

        for (Literal cur : c.getLiterals()) {
          if (cur.equalToAny(literals)) {
            shouldAddClause = false;
          } else if (!cur.equalToAnyOppositeSign(literals)) {
            newClause.addToSet(cur);
          }
        }
        if (shouldAddClause) {
          reconstructed.addToFormula(newClause);
        }
      } else {
        reconstructed.addToFormula(c);
      }
    }
    return reconstructed;
  }

  /**
   * Finds the literals that are pure in the formula.
   */
  private Set<Literal> pureLiterals(Formula f) {
    Set<Literal> l = new HashSet<>();
    for (Integer in : f.getVars()) {
      boolean foundPos = false;
      boolean foundNeg = false;
      for (Clause c : f.getFormula()) {
        for (Literal lit : c.getLiterals()) {
          if (lit.getVal().compareTo(in) == 0) {
            if (lit.getSign()) { foundPos = true; }
            else { foundNeg = true; }
          }
        }
      }
      if ((foundPos || foundNeg) && !(foundPos && foundNeg)) {
        if (foundPos) {
          l.add(new Literal(true, in));
        } else {
          l.add(new Literal(false, in));
        }
      }
    }
    return l;
  }

  /**
   * Finds the literals that are in unit clauses in formula
   */
  private Set<Literal> unitClauses(Formula f) {
    Set<Literal> s = new HashSet<>();
    for (Clause c : f.getFormula()) {
      if (c.getLiterals().size() == 1) {
        for (Literal l : c.getLiterals()) {
          s.add(l);
        }
      }
    }
    return s;
  }

  private void formatOutput(Map<Integer, Boolean> literals) {
    List<String> trueLits = new ArrayList<>();
    List<String> falseLits = new ArrayList<>();
    literals.forEach((variable, sign) -> {
      if (sign) {
        trueLits.add("" + variable);
      } else {
        falseLits.add("-" + variable);
      }
    });
    System.out.println(String.join(" ", trueLits));
    System.out.println(String.join(" ", falseLits));

  }

  public static void main(String[] args) throws IOException {

    SATSolver sat = new SATSolver();

    Formula formula = sat.createFormula();

    //this reader assumes PERFECT input
    try (BufferedReader reader = new BufferedReader(new InputStreamReader(System.in))) {
      String line;
      while ((line = reader.readLine()) != null) {
        String[] pieces = line.split(" ");
        Clause clause = sat.createClause();
        for (String s : pieces) {
          s = s.trim();
          if (!(s.startsWith("-")) && s.length() > 0) {
            clause.getLiterals().add(sat.createLiteral(true, s));
          } else if (s.startsWith("-")) {
            String cut = s.substring(1, s.length());
            clause.getLiterals().add(sat.createLiteral(false, cut));
          }
        }
        formula.getFormula().add(clause);
      }
      reader.close();
    }

    
    Map<Integer, Boolean> solved = sat.solve(formula);
    if (solved != null) {
      sat.formatOutput(sat.solve(formula));
    } else {
      System.out.println("unsat");
    }
  }
}






