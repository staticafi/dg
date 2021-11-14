#ifndef DG_LLVM_VALUE_RELATIONS_VR_H_
#define DG_LLVM_VALUE_RELATIONS_VR_H_

#include <llvm/IR/Constants.h>
#include <llvm/IR/Value.h>

#include <map>

#ifndef NDEBUG
#include "getValName.h"
#include <iostream>
#endif

#include "dg/ValueRelations/RelationsGraph.h"

namespace dg {
namespace vr {

struct VR {
    using RelGraph = RelationsGraph<VR>;
    using Handle = const Bucket &;
    using RelationsMap = RelGraph::RelationsMap;
    using V = const llvm::Value *;
    using C = const llvm::ConstantInt *;

  private:
    using BareC = llvm::ConstantInt;
    using HandlePtr = const Bucket *;
    using BRef = std::reference_wrapper<const Bucket>;

    template <typename T>
    friend class RelationsGraph;
    friend class ValueIterator;

    RelGraph graph;

    std::map<V, BRef> valToBucket;
    std::map<BRef, std::set<V>> bucketToVals;
    std::vector<bool> validAreas;

    bool changed = false;

    // ****************************** get ********************************* //
    HandlePtr maybeGet(Handle h) const { return &h; }
    HandlePtr maybeGet(V val) const;

    Handle get(Handle h) const { return h; }
    Handle get(V val);

    V getAny(Handle h) const;
    VR::C getAnyConst(Handle h) const;

    std::vector<V> getDirectlyRelated(V val, const Relations &rels) const;
    std::pair<VR::C, Relations> getBound(Handle h, Relations rel) const;
    std::pair<VR::C, Relations> getBound(V val, Relations rel) const;

    HandlePtr getHandleByPtr(Handle h) const;

    // ************************** general set ***************************** //
    template <typename X, typename Y>
    void set(const X &lt, Relations::Type rel, const Y &rt) {
        bool ch = graph.addRelation(get(lt), rel, get(rt));
        updateChanged(ch);
    }

    // ************************* general unset **************************** //
    void unset(Relations rels) {
        bool ch = graph.unset(rels);
        updateChanged(ch);
    }
    void unset(Relations::Type rel) { unset(Relations().set(rel)); }
    template <typename X>
    void unset(const X &val, Relations rels) {
        bool ch = graph.unset(get(val), rels);
        updateChanged(ch);
    }
    template <typename X>
    void unset(const X &val, Relations::Type rel) {
        unset(val, Relations().set(rel));
    }

    // ************************** general are ***************************** //
    bool _are(Handle lt, Relations::Type rel, Handle rt) const;
    bool _are(Handle lt, Relations::Type rel, V rt) const;
    bool _are(Handle lt, Relations::Type rel, C rt) const;
    bool _are(V lt, Relations::Type rel, Handle rt) const;
    bool _are(C lt, Relations::Type rel, Handle rt) const;
    bool _are(V lt, Relations::Type rel, V rt) const;

    // ************************** general has ***************************** //
    template <typename X>
    bool has(const X &val, Relations::Type rel) const {
        HandlePtr mVal = maybeGet(val);
        return mVal && mVal->hasRelation(rel);
    }
    template <typename X>
    bool has(const X &val, Relations rels) const {
        HandlePtr mVal = maybeGet(val);
        return mVal && mVal->hasAnyRelation(rels);
    }

    // *************************** iterators ***************************** //
    class RelatedValueIterator {
        using RelatedIterator = RelationsMap::iterator;
        using ValIterator = typename std::set<V>::const_iterator;

        const VR &vr;

        RelationsMap related;
        RelatedIterator bucketIt;
        ValIterator valueIt;

        std::pair<V, Relations::Type> current; // Relations>;

        bool isEnd = false;

        const std::set<V> &getCurrentEqual() const {
            return vr.bucketToVals.find(bucketIt->first)->second;
        }

        void updateCurrent() {
            current = std::make_pair(*valueIt, bucketIt->second.get());
        }

        void nextViableValue() {
            while (valueIt == getCurrentEqual().end()) {
                ++bucketIt;
                if (bucketIt == related.end()) {
                    isEnd = true;
                    return;
                }
                valueIt = getCurrentEqual().begin();
            }
        }

      public:
        using value_type = decltype(current);
        using difference_type = int64_t;
        using iterator_category = std::input_iterator_tag;

        using reference = value_type &;
        using pointer = value_type *;

        // for end iterator
        RelatedValueIterator(const VR &v) : vr(v), isEnd(true) {}
        // for begin iterator
        RelatedValueIterator(const VR &v, Handle start,
                             const Relations &allowedEdges)
                : vr(v), related(vr.graph.getRelated(start, allowedEdges)),
                  bucketIt(related.begin()),
                  valueIt(getCurrentEqual().begin()) {
            assert(allowedEdges.has(Relations::EQ) &&
                   "at least one related bucket");
            nextViableValue();
        }

        friend bool operator==(const RelatedValueIterator &lt,
                               const RelatedValueIterator &rt) {
            return (lt.isEnd && rt.isEnd) ||
                   (!lt.isEnd && !rt.isEnd && lt.bucketIt == rt.bucketIt &&
                    lt.valueIt == rt.valueIt);
        }
        friend bool operator!=(const RelatedValueIterator &lt,
                               const RelatedValueIterator &rt) {
            return !(lt == rt);
        }

        RelatedValueIterator &operator++() {
            ++valueIt;
            nextViableValue();
            return *this;
        }
        RelatedValueIterator operator++(int) {
            auto copy = *this;
            ++*this;
            return copy;
        }

        reference operator*() { return current; }
        pointer operator->() { return &current; }
    };

    class PlainValueIterator {
        using BucketIterator = std::map<BRef, std::set<V>>::const_iterator;
        using ValIterator = std::set<V>::iterator;

        BucketIterator bucketIt;
        BucketIterator endIt;
        ValIterator valueIt;

        bool nextViableValue() {
            while (valueIt == bucketIt->second.end()) {
                if (++bucketIt == endIt)
                    return false;
                valueIt = bucketIt->second.begin();
            }
            return true;
        }

      public:
        using value_type = V;
        using difference_type = int64_t;
        using iterator_category = std::input_iterator_tag;

        using reference = value_type;
        using pointer = const value_type *;

        // for end iterator
        PlainValueIterator(BucketIterator e) : bucketIt(e) {}
        // for begin iterator
        PlainValueIterator(BucketIterator b, BucketIterator e)
                : bucketIt(b), endIt(e), valueIt(b->second.begin()) {
            nextViableValue();
        }

        friend bool operator==(const PlainValueIterator &lt,
                               const PlainValueIterator &rt) {
            return lt.bucketIt == rt.bucketIt;
        }
        friend bool operator!=(const PlainValueIterator &lt,
                               const PlainValueIterator &rt) {
            return !(lt == rt);
        }

        PlainValueIterator &operator++() {
            ++valueIt;
            nextViableValue();
            return *this;
        }

        PlainValueIterator operator++(int) {
            auto copy = *this;
            ++*this;
            return copy;
        }

        reference operator*() const { return *valueIt; }
        pointer operator->() const { return &(*valueIt); }
    };

    // ***************************** other ******************************** //
    static bool compare(C lt, Relations::Type rel, C rt);
    static bool compare(C lt, Relations rels, C rt);
    Handle getCorresponding(const VR &other, Handle otherH,
                            const std::vector<V> &otherEqual);
    Handle getCorresponding(const VR &other, Handle otherH);
    Handle getAndMerge(const VR &other, Handle current);
    Handle add(V val, Handle h, std::set<V> &vals);
    Handle add(V val, Handle h);
    void areMerged(Handle to, Handle from);
    void updateChanged(bool ch) { changed |= ch; }

  public:
    VR() : graph(*this) {}
    VR(const VR &) = delete;

    using rel_iterator = RelatedValueIterator;
    using plain_iterator = PlainValueIterator;

    // ****************************** set ********************************* //
    template <typename X, typename Y>
    void setEqual(const X &lt, const Y &rt) {
        set(lt, Relations::EQ, rt);
    }
    template <typename X, typename Y>
    void setNonEqual(const X &lt, const Y &rt) {
        set(lt, Relations::NE, rt);
    }
    template <typename X, typename Y>
    void setLesser(const X &lt, const Y &rt) {
        set(lt, Relations::LT, rt);
    }
    template <typename X, typename Y>
    void setLesserEqual(const X &lt, const Y &rt) {
        set(lt, Relations::LE, rt);
    }
    template <typename X, typename Y>
    void setLoad(const X &from, const Y &to) {
        set(from, Relations::PT, to);
    }
    // void setLesserEqual(V lt, Handle rt) { set(lt, Relations::LE, rt); }

    // ***************************** unset ******************************** //
    template <typename X>
    void unsetAllLoadsByPtr(const X &from) {
        unset(from, Relations::PT);
    }
    void unsetAllLoads() { unset(Relations::PT); }
    template <typename X>
    void unsetComparativeRelations(const X &val) {
        unset(val, comparative);
    }

    // ******************************* is ********************************** //
    template <typename X, typename Y>
    bool are(const X &lt, Relations::Type rel, const Y &rt) const {
        return _are(lt, rel, rt);
    }
    template <typename X, typename Y>
    bool isEqual(const X &lt, const Y &rt) const {
        return are(lt, Relations::EQ, rt);
    }
    template <typename X, typename Y>
    bool isNonEqual(const X &lt, const Y &rt) const {
        return are(lt, Relations::NE, rt);
    }
    template <typename X, typename Y>
    bool isLesser(const X &lt, const Y &rt) const {
        return are(lt, Relations::LT, rt);
    }
    template <typename X, typename Y>
    bool isLesserEqual(const X &lt, const Y &rt) const {
        return are(lt, Relations::LE, rt);
    }
    template <typename X, typename Y>
    bool isLoad(const X &from, const Y &to) const {
        return are(from, Relations::PT, to);
    }

    // ****************************** has ********************************* //
    template <typename X>
    bool hasLoad(const X &from) const {
        return has(from, Relations::PT);
    }
    template <typename X, typename Y>
    bool haveConflictingRelations(const X &lt, Relations::Type rel,
                                  const Y &rt) const {
        HandlePtr mLt = maybeGet(lt);
        HandlePtr mRt = maybeGet(rt);

        return mLt && mRt && graph.haveConflictingRelation(*mLt, rel, *mRt);
    }
    template <typename X, typename Y>
    bool hasConflictingRelation(const X &lt, const Y &rt,
                                Relations::Type rel) const {
        return haveConflictingRelations(lt, rel, rt);
    }
    template <typename X>
    bool hasComparativeRelations(const X &val) const {
        return has(val, comparative);
    }

    // *************************** iterators ****************************** //
    rel_iterator begin_related(V val,
                               const Relations &rels = allRelations) const;
    rel_iterator end_related(V val) const;

    RelGraph::iterator
    begin_related(Handle h, const Relations &rels = allRelations) const;
    RelGraph::iterator end_related(Handle h) const;

    rel_iterator begin_all(V val) const;
    rel_iterator end_all(V val) const;

    rel_iterator begin_lesserEqual(V val) const;
    rel_iterator end_lesserEqual(V val) const;

    plain_iterator begin() const;
    plain_iterator end() const;

    RelGraph::iterator
    begin_buckets(const Relations &rels = allRelations) const;
    RelGraph::iterator end_buckets() const;

    // ****************************** get ********************************* //
    std::vector<V> getEqual(Handle h) const;
    std::vector<V> getEqual(V val) const;

    std::vector<V> getAllRelated(V val) const;
    template <typename X>
    RelGraph::RelationsMap getAllRelated(const X &val) const {
        HandlePtr mH = maybeGet(val);
        assert(mH);
        return graph.getRelated(*mH, allRelations);
    }
    std::vector<V> getAllValues() const;

    std::vector<V> getDirectlyLesser(V val) const;
    std::vector<V> getDirectlyGreater(V val) const;

    std::pair<C, Relations> getLowerBound(V val) const;
    std::pair<C, Relations> getUpperBound(V val) const;

    C getLesserEqualBound(V val) const;
    C getGreaterEqualBound(V val) const;

    const std::vector<V> getValsByPtr(V from) const;

    std::set<std::pair<std::vector<V>, std::vector<V>>> getAllLoads() const;

    std::vector<bool> &getValidAreas() { return validAreas; }
    const std::vector<bool> &getValidAreas() const { return validAreas; }

    // ************************** placeholder ***************************** //
    Handle newPlaceholderBucket();
    void erasePlaceholderBucket(Handle id);

    // ***************************** other ******************************** //
    bool merge(const VR &other, Relations relations = allRelations);
    VR &unsetChanged() {
        changed = false;
        return *this;
    }
    bool hasChanged() { return changed; }
    bool holdsAnyRelations() const;

#ifndef NDEBUG
    friend std::ostream &operator<<(std::ostream &out, const VR &vr);
#endif
};

} // namespace vr
} // namespace dg

#endif // DG_LLVM_VALUE_RELATIONS_VR_H_