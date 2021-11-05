#ifndef __LemmasIterators__
#define __LemmasIterators__

#include <memory>
#include <vector>

#include "Problem.hpp"
#include "Program.hpp"
#include "ProgramTraverser.hpp"

namespace analysis {

/*
 * We use the lemmas in this header to cover the inductive reasoning for
 * iterator variables.
 *
 * An iterator variable is a variable which iterates through a datastructure. We
 * currently don't support any datastructure other than arrays.
 *
 * We assume that any non-array variable potentially is an iterator variable.
 * In the future, one could also add an explicit iterator-type (as in C++) to
 * the input-language, and add iterator lemmas only for those variables. This
 * would introduce less useless lemmas, but would burden the programmer with
 * explicitly marking the iterator-variables.
 */

/*
 * LEMMA 1:
 * If the (iterator-) variable v is dense, and the value x is between the value
 * of v at the beginning and at the end of the loop, then there is a timepoint
 * in the loop, where v has value x. The value x usually denotes some position
 * in an array. One can see this lemma as a discrete version of the Intermediate
 * Value Theorem for continuous functions. (added for both non-array- and array
 * variables. we ignore array positions and enclosing iterators in this
 * description)
 *
 * forall x.
 *    =>
 *       Prem(x)
 *       exists it2.
 *          and
 *             it2<n
 *             v(l(it2))=x
 *             v(l(s(it2)))=v(l(it2))+1
 * where:
 * - Prem(x) :=
 *   and
 *      v(l(zero))<=x
 *      x<v(l(n))
 *      Dense_v
 * - Dense_v :=
 *   forall it.
 *      =>
 *         it<n
 *         or
 *            v(l(s(it)))=v(l(it))
 *            v(l(s(it)))=v(l(it))+1
 *
 * Soundness: The lemma is equivalent (by using modus tollens and inlining
 * definitions) to the following lemma 1A: forall x.
 *    =>
 *       and
 *          v(l(zero))<=x
 *          forall it.
 *             =>
 *                it<n
 *                or
 *                   v(l(s(it)))=v(l(it))
 *                   v(l(s(it)))=v(l(it))+1
 *          forall it2.
 *             =>
 *                and
 *                   it2<n
 *                   v(l(s(it2)))=v(l(it2))+1
 *                v(l(it2))!=x
 *       v(l(n))<=x
 * Lemma 1A follows from the following lemma 1B:
 * forall x.
 *    =>
 *       and
 *          v(l(zero))<=x
 *          forall it.
 *             =>
 *                it<n
 *                v(l(it))<=x
 *             v(l(s(it)))<=x
 *       forall it.
 *          =>
 *             it<n
 *             v(l(s(it)))<=x
 * Lemma 1B follows from the standard induction axiom by
 * - substituting boundL->zero, boundR->n
 * - defining P(it) := v(l(it))<=x
 * - applying simplifications which use the fact that 0 is the smallest natural
 * number.
 *
 * Discussion on possible Variations:
 *  TODO: one could make the lemma more general by generalizing zero and n to
 * boundL and boundR. Would this result in a better or simpler encoding of the
 * synchronization of the two orderings?
 *
 * Why is this lemma useful:
 *  This lemma synthesizes interesting timepoints, which can be used to split a
 * loop into intervals. Often the timepoints in such an interval behave in some
 * uniform way, and if this is the case then we often can apply other induction
 * lemmas to the interval.
 */
class IntermediateValueLemmas
    : public ProgramTraverser<
          std::vector<std::shared_ptr<const logic::ProblemItem>>> {
 public:
  using ProgramTraverser::ProgramTraverser;  // inherit initializer, note:
                                             // doesn't allow additional members
                                             // in subclass!

 private:
  virtual void generateOutputFor(
      const program::WhileStatement* statement,
      std::vector<std::shared_ptr<const logic::ProblemItem>>& items) override;
};

/*
 * LEMMA 2:
 * =>
 *    and
 *       Dense_v
 *       v(l(s(it1)))=v(l(it1))+1
 *       it1<it2
 *       it2<=n
 *    v(l(it1))!=v(l(it2))
 * where:
 * - Dense_v :=
 *   forall it.
 *      =>
 *         it<n
 *         or
 *            v(l(s(it)))=v(l(it))
 *            v(l(s(it)))=v(l(it))+1
 *
 * Soundness:
 * This lemma uses the following instance of the standard induction axiom
 * - substitute boundL->s(it1), boundR->it2
 * - define P(it) := v(l(it1))<v(l(it))
 * It uses the following theory axioms for Nat:
 * - transitivity for Nat (for the variant <=,<)
 * - monotonicity of s with respect to <
 * It uses he following theory axioms for Int:
 * - forall x: x<x+1
 * - transitivity for Int (for the variant <,<)
 * - x<y => x!=y
 *
 * Possible Variations
 * - We could use v(l(it1))<v(l(it2)) as conclusion instead of the logically
 * weaker v(l(it1))!=v(l(it2)). It is again unclear whether this would make
 * things better or worse. Note that the resulting lemma would be similar to the
 * value-evolution lemmas (but applied to the non-reflexive relation <)
 *
 * Why is this lemma useful:
 *  Iterators often have the property that they visit each element of the
 * datastructure at most once. This lemmas states that an array-iterator, which
 * increases by 1 each iteration, visits each array-position at most once. If
 * each array-position is visited only once, we know that its value is not
 * changed after the first visit, and in particular the value at the end is the
 * value after the first visit.
 */
class IterationInjectivityLemmas
    : public ProgramTraverser<
          std::vector<std::shared_ptr<const logic::ProblemItem>>> {
 public:
  using ProgramTraverser::ProgramTraverser;  // inherit initializer, note:
                                             // doesn't allow additional members
                                             // in subclass!

 private:
  virtual void generateOutputFor(
      const program::WhileStatement* statement,
      std::vector<std::shared_ptr<const logic::ProblemItem>>& items) override;
};
}  // namespace analysis

#endif
