#include <llvm/IR/Instructions.h>
#include <llvm/Support/raw_ostream.h>

#include <iostream>
#include <sstream>

#include "Node.h"

using namespace std;
using namespace llvm;

int Node::lastId = 0;

Node::Node(NodeType type, const Instruction *instruction,
           const CallInst *callInst)
        : id_(lastId++), nodeType_(type), llvmInstruction_(instruction),
          callInstruction_(callInst) {}

NodeIterator Node::begin() const { return NodeIterator(this, true); }

NodeIterator Node::end() const { return NodeIterator(this, false); }

int Node::id() const { return id_; }

NodeType Node::getType() const { return nodeType_; }

string Node::dotName() const { return "NODE" + to_string(id_); }

bool Node::addPredecessor(Node *node) {
    if (!node) {
        return false;
    }
    predecessors_.insert(node);
    return node->successors_.insert(this).second;
}

bool Node::addSuccessor(Node *node) {
    if (!node) {
        return false;
    }
    successors_.insert(node);
    return node->predecessors_.insert(this).second;
}

bool Node::removePredecessor(Node *node) {
    if (!node) {
        return false;
    }
    predecessors_.erase(node);
    return node->successors_.erase(this);
}

bool Node::removeSuccessor(Node *node) {
    if (!node) {
        return false;
    }
    successors_.erase(node);
    return node->predecessors_.erase(this);
}

const set<Node *> &Node::predecessors() const { return predecessors_; }

const set<Node *> &Node::successors() const { return successors_; }

size_t Node::predecessorsNumber() const { return predecessors_.size(); }

size_t Node::successorsNumber() const { return predecessors_.size(); }

void Node::addCallPredecessor(Node *node) {
    directCallPredecessors_.insert(node);
}

std::set<Node *> Node::directPredecessors() const {
    std::set<Node *> res;

    if (getType() == NodeType::ENTRY) {
        return res;
    }

    for (auto *pred : predecessors()) {
        if (pred->getType() == NodeType::EXIT) {
            continue;
        }

        res.insert(pred);
    }

    for (auto *pred : directCallPredecessors_) {
        res.insert(pred);
    }

    return res;
}

std::set<Node *> Node::directSuccessors() const {
    return successors();
}

bool Node::isArtificial() const { return llvmInstruction_ == nullptr; }

const Instruction *Node::llvmInstruction() const { return llvmInstruction_; }

const CallInst *Node::callInstruction() const {
    if (callInstruction_) {
        return callInstruction_;
    }
    if (llvmInstruction_) {
        return llvm::dyn_cast<llvm::CallInst>(llvmInstruction_);
    }
    return nullptr;
}

string Node::dump() const {
    return this->dotName() + " " + this->label() + "\n";
}

string Node::label() const {
    std::string label_ = "[label=\"<" + std::to_string(this->id()) + "> " +
                         nodeTypeToString(this->getType());
    if (!isArtificial()) {
        string llvmTemporaryString;
        raw_string_ostream llvmStream(llvmTemporaryString);
        llvmInstruction_->print(llvmStream);
        label_ += "\n" + llvmTemporaryString;
    }
    label_ += " \"]";
    return label_;
}

void Node::printOutcomingEdges(ostream &ostream, bool printOnlyDirect) const {
    if (!printOnlyDirect) {
        for (const auto &successor : successors_) {
            ostream << this->dotName() << " -> " << successor->dotName() << "\n";
        }
    }

    for (auto *directSuccessor : directSuccessors()) {
        ostream << this->dotName() << " -> " << directSuccessor->dotName() << " [color=\"red\"]\n";
    }
}
