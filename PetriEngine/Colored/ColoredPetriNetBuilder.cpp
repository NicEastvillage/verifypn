/*
 * File:   ColoredPetriNetBuilder.cpp
 * Author: Klostergaard
 * 
 * Created on 17. februar 2018, 16:25
 */

#include "ColoredPetriNetBuilder.h"
#include <chrono>

namespace PetriEngine {
    ColoredPetriNetBuilder::ColoredPetriNetBuilder() {
    }

    ColoredPetriNetBuilder::ColoredPetriNetBuilder(const ColoredPetriNetBuilder& orig) {
    }

    ColoredPetriNetBuilder::~ColoredPetriNetBuilder() {
    }

    void ColoredPetriNetBuilder::addPlace(const std::string& name, int tokens, double x, double y) {
        if (!_isColored) {
            _ptBuilder.addPlace(name, tokens, x, y);
        }
    }

    void ColoredPetriNetBuilder::addPlace(const std::string& name, Colored::ColorType* type, Colored::Multiset tokens, double x, double y) {
        if(_placenames.count(name) == 0)
        {
            uint32_t next = _placenames.size();
            _places.push_back(Colored::Place {name, type, tokens});
            _placenames[name] = next;
        }
    }

    void ColoredPetriNetBuilder::addTransition(const std::string& name, double x, double y) {
        if (!_isColored) {
            _ptBuilder.addTransition(name, x, y);
        }
    }

    void ColoredPetriNetBuilder::addTransition(const std::string& name, Colored::GuardExpression_ptr guard, double x, double y) {
        if(_transitionnames.count(name) == 0)
        {
            uint32_t next = _transitionnames.size();
            _transitions.push_back(Colored::Transition {name, guard});
            _transitionnames[name] = next;
        }
    }

    void ColoredPetriNetBuilder::addInputArc(const std::string& place, const std::string& transition, bool inhibitor, int weight) {
        if (!_isColored) {
            _ptBuilder.addInputArc(place, transition, inhibitor, weight);
        }
    }

    void ColoredPetriNetBuilder::addInputArc(const std::string& place, const std::string& transition, Colored::ArcExpression_ptr expr) {
        addArc(place, transition, expr, true);
    }

    void ColoredPetriNetBuilder::addOutputArc(const std::string& transition, const std::string& place, int weight) {
        if (!_isColored) {
            _ptBuilder.addOutputArc(transition, place, weight);
        }
    }

    void ColoredPetriNetBuilder::addOutputArc(const std::string& transition, const std::string& place, Colored::ArcExpression_ptr expr) {
        addArc(place, transition, expr, false);
    }

    void ColoredPetriNetBuilder::addArc(const std::string& place, const std::string& transition, Colored::ArcExpression_ptr expr, bool input) {
        if(_transitionnames.count(transition) == 0)
        {
            std::cout << "Transition '" << transition << "' not found. Adding it." << std::endl;
            addTransition(transition,0.0,0.0);
        }
        if(_placenames.count(place) == 0)
        {
            std::cout << "Place '" << place << "' not found. Adding it." << std::endl;
            addPlace(place,0,0,0);
        }
        uint32_t p = _placenames[place];
        uint32_t t = _transitionnames[transition];

        assert(t < _transitions.size());
        assert(p < _places.size());

        Colored::Arc arc;
        arc.place = p;
        arc.transition = t;
        assert(expr != nullptr);
        arc.expr = std::move(expr);
        arc.input = input;
        _transitions[t].arcs.push_back(std::move(arc));
        //_arcs.push_back(arc);
    }

    void ColoredPetriNetBuilder::addColorType(const std::string& id, Colored::ColorType* type) {
        _colors[id] = type;
    }

    void ColoredPetriNetBuilder::sort() {

    }

    PetriNetBuilder& ColoredPetriNetBuilder::unfold() {
        if (_stripped) assert(false);
        if (_isColored && !_unfolded) {
            auto start = std::chrono::high_resolution_clock::now();
            for (auto& place : _places) {
                unfoldPlace(place);
            }

            for (auto& transition : _transitions) {
                std::cout << "Unfolding transition: " << transition.name << std::endl;
                unfoldTransition(transition);
            }

            /*for (auto& arc : _arcs) {
                unfoldArc(arc);
            }*/
            _unfolded = true;
            auto end = std::chrono::high_resolution_clock::now();
            _time = (std::chrono::duration_cast<std::chrono::microseconds>(end - start).count())*0.000001;
        }

        return _ptBuilder;
    }

    void ColoredPetriNetBuilder::unfoldPlace(Colored::Place& place) {
        for (size_t i = 0; i < place.type->size(); ++i) {
            std::string name = place.name + ";" + std::to_string(i);
            const Colored::Color* color = &(*place.type)[i];
            _ptBuilder.addPlace(name, place.marking[color], 0.0, 0.0);
            _ptplacenames[place.name][color->getId()] = name;
            ++_nptplaces;
        }
    }

    void ColoredPetriNetBuilder::unfoldTransition(Colored::Transition& transition) {
        BindingGenerator gen(transition, _arcs, _colors);
        size_t i = 0;
        for (auto& b : gen) {
            //size_t i = transition.bindings.size();
            std::unordered_map<std::string, const Colored::Color*> binding;
            for (auto& elem : b) {
                binding[elem.var->name] = elem.color;
            }
            //transition.bindings.push_back(binding);
            std::string name = transition.name + ";" + std::to_string(i++);
            _ptBuilder.addTransition(name, 0.0, 0.0);
            //_pttransitionnames[transition.name].push_back(name);
            ++_npttransitions;
            for (auto& arc : transition.arcs) {
                unfoldArc(arc, binding, name);
            }
        }
    }

    void ColoredPetriNetBuilder::unfoldArc(Colored::Arc& arc, std::unordered_map<std::string, const Colored::Color*> binding, std::string tName) {
        //Colored::Transition& transition = _transitions[arc.transition];
        //for (size_t i = 0; i < transition.bindings.size(); ++i) {
            Colored::ExpressionContext context {binding, _colors};
            Colored::Multiset ms = arc.expr->eval(context);

            for (const auto& color : ms) {
                if (color.second == 0) {
                    continue;
                }

                std::string pName = _ptplacenames[_places[arc.place].name][color.first->getId()];
                //std::string tName = _pttransitionnames[transition.name][i];

                if (arc.input) {
                    _ptBuilder.addInputArc(pName, tName, false, color.second);
                } else {
                    _ptBuilder.addOutputArc(tName, pName, color.second);
                }
                ++_nptarcs;
            }
        //}
    }

    PetriNetBuilder& ColoredPetriNetBuilder::stripColors() {
        if (_unfolded) assert(false);
        if (_isColored && !_stripped) {
            for (auto& place : _places) {
                _ptBuilder.addPlace(place.name, place.marking.size(), 0.0, 0.0);
            }

            for (auto& transition : _transitions) {
                _ptBuilder.addTransition(transition.name, 0.0, 0.0);
            }

            for (auto& arc : _arcs) {
                try {
                    if (arc.input) {
                        _ptBuilder.addInputArc(_places[arc.place].name, _transitions[arc.transition].name, false,
                                               arc.expr->weight());
                    } else {
                        _ptBuilder.addOutputArc(_transitions[arc.transition].name, _places[arc.place].name,
                                                arc.expr->weight());
                    }
                } catch (Colored::WeightException& e) {
                    std::cerr << "Exception on arc: " << arcToString(arc) << std::endl;
                    std::cerr << "In expression: " << arc.expr->toString() << std::endl;
                    std::cerr << e.what() << std::endl;
                    exit(ErrorCode);
                }
            }
            _stripped = true;
            _isColored = false;
        }

        return _ptBuilder;
    }

    std::string ColoredPetriNetBuilder::arcToString(Colored::Arc& arc) const {
        return !arc.input ? "(" + _transitions[arc.transition].name + ", " + _places[arc.place].name + ")" :
               "(" + _places[arc.place].name + ", " + _transitions[arc.transition].name + ")";
    }

    BindingGenerator::Iterator::Iterator(BindingGenerator* generator)
            : _generator(generator)
    {
    }

    bool BindingGenerator::Iterator::operator==(Iterator& other) {
        return _generator == other._generator;
    }

    bool BindingGenerator::Iterator::operator!=(Iterator& other) {
        return _generator != other._generator;
    }

    BindingGenerator::Iterator& BindingGenerator::Iterator::operator++() {
        _generator->nextBinding();
        if (_generator->isInitial()) _generator = nullptr;
        return *this;
    }

    std::vector<Colored::Binding> BindingGenerator::Iterator::operator++(int) {
        auto prev = _generator->currentBinding();
        ++*this;
        return prev;
    }

    std::vector<Colored::Binding>& BindingGenerator::Iterator::operator*() {
        return _generator->currentBinding();
    }

    BindingGenerator::BindingGenerator(Colored::Transition& transition,
            const std::vector<Colored::Arc>& arcs,
            ColoredPetriNetBuilder::ColorTypeMap& colorTypes)
        : _colorTypes(colorTypes)
    {
        _expr = transition.guard;
        std::set<Colored::Variable*> variables;
        if (_expr != nullptr) {
            _expr->getVariables(variables);
        }
        for (auto arc : transition.arcs) {
            assert(arc.expr != nullptr);
            arc.expr->getVariables(variables);
        }
        for (auto var : variables) {
            _bindings.push_back(Colored::Binding {var, &(*var->colorType)[0]});
        }
        
        if (!eval())
            nextBinding();
    }

    bool BindingGenerator::eval() {
        if (_expr == nullptr)
            return true;

        std::unordered_map<std::string, const Colored::Color*> binding;
        for (auto& elem : _bindings) {
            binding[elem.var->name] = elem.color;
        }
        Colored::ExpressionContext context {binding, _colorTypes};
        return _expr->eval(context);
    }
    
    std::vector<Colored::Binding>& BindingGenerator::nextBinding() {
        bool test = false;
        while (!test) {
            for (size_t i = 0; i < _bindings.size(); ++i) {
                _bindings[i].color = &++(*_bindings[i].color);
                if (_bindings[i].color->getId() != 0) {
                    break;
                }
            }

            if (isInitial())
                break;

            test = eval();
        }
        return _bindings;
    }

    std::vector<Colored::Binding>& BindingGenerator::currentBinding() {
        return _bindings;
    }

    bool BindingGenerator::isInitial() const {
        for (auto& b : _bindings) {
            if (b.color->getId() != 0) return false;
        }
        return true;
    }

    BindingGenerator::Iterator BindingGenerator::begin() {
        return Iterator(this);
    }

    BindingGenerator::Iterator BindingGenerator::end() {
        return Iterator(nullptr);
    }
}

