/* Copyright (C) 2020  Alexander Bilgram <alexander@bilgram.dk>,
 *                     Peter Haar Taankvist <ptaankvist@gmail.com>,
 *                     Thomas Pedersen <thomas.pedersen@stofanet.dk>
 *                     Andreas H. Klostergaard
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "PetriEngine/Colored/ColoredPetriNetBuilder.h"
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

    void ColoredPetriNetBuilder::addPlace(const std::string& name, Colored::ColorType* type, Colored::Multiset&& tokens, double x, double y) {
        if(_placenames.count(name) == 0)
        {
            uint32_t next = _placenames.size();
            _places.emplace_back(Colored::Place {name, type, tokens});
            _placenames[name] = next;

            //set up place color fix points and initialize queue
            if (!tokens.empty()) {
                _placeFixpointQueue.emplace_back(next);
            }

            Colored::intervalTuple_t placeConstraints;
            Colored::ColorFixpoint colorFixpoint = {placeConstraints, !tokens.empty()};

            if(tokens.size() == type->size()){
                colorFixpoint.constraints.addInterval(type->getFullInterval());
            } else {
                uint32_t index = 0;
                for (auto colorPair : tokens) {
                    Colored::interval_t tokenConstraints;
                    colorPair.first->getColorConstraints(&tokenConstraints, &index);

                    colorFixpoint.constraints.addInterval(tokenConstraints);
                    index = 0;
                }
            }
         
            _placeColorFixpoints.push_back(colorFixpoint);            
        }
    }

    void ColoredPetriNetBuilder::addTransition(const std::string& name, double x, double y) {
        if (!_isColored) {
            _ptBuilder.addTransition(name, x, y);
        }
    }

    void ColoredPetriNetBuilder::addTransition(const std::string& name, const Colored::GuardExpression_ptr& guard, double x, double y) {
        if(_transitionnames.count(name) == 0)
        {
            uint32_t next = _transitionnames.size();
            _transitions.emplace_back(Colored::Transition {name, guard});
            _transitionnames[name] = next;
        }
    }

    void ColoredPetriNetBuilder::addInputArc(const std::string& place, const std::string& transition, bool inhibitor, int weight) {
        if (!_isColored) {
            _ptBuilder.addInputArc(place, transition, inhibitor, weight);
        }
    }

    void ColoredPetriNetBuilder::addInputArc(const std::string& place, const std::string& transition, const Colored::ArcExpression_ptr& expr) {
        addArc(place, transition, expr, true);
    }

    void ColoredPetriNetBuilder::addOutputArc(const std::string& transition, const std::string& place, int weight) {
        if (!_isColored) {
            _ptBuilder.addOutputArc(transition, place, weight);
        }
    }

    void ColoredPetriNetBuilder::addOutputArc(const std::string& transition, const std::string& place, const Colored::ArcExpression_ptr& expr) {
        addArc(place, transition, expr, false);
    }

    void ColoredPetriNetBuilder::addArc(const std::string& place, const std::string& transition, const Colored::ArcExpression_ptr& expr, bool input) {
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

        input? _placePostTransitionMap[p].emplace_back(t): _placePreTransitionMap[p].emplace_back(t);

        Colored::Arc arc;
        arc.place = p;
        arc.transition = t;
        assert(expr != nullptr);
        arc.expr = std::move(expr);
        arc.input = input;
        input? _transitions[t].input_arcs.push_back(std::move(arc)): _transitions[t].output_arcs.push_back(std::move(arc));
    }

    void ColoredPetriNetBuilder::addColorType(const std::string& id, Colored::ColorType* type) {
        _colors[id] = type;
    }

    void ColoredPetriNetBuilder::sort() {
    }

    //----------------------- Color fixpoint -----------------------//

    void ColoredPetriNetBuilder::printPlaceTable() {
        for (auto place: _places) {
            auto placeID = _placenames[place.name];
            auto placeColorFixpoint = _placeColorFixpoints[placeID];
            std::cout << "Place: " << place.name << " in queue: " << placeColorFixpoint.inQueue  << " with colortype " << place.type->getName() << std::endl;

            for(auto fixpointPair : placeColorFixpoint.constraints._intervals) {
                std::cout << "[";
                for(auto range : fixpointPair._ranges) {
                    std::cout << range._lower << "-" << range._upper << ", ";
                }
                std::cout << "]"<< std::endl;                    
            }
            std::cout << std::endl;
        }
    }

    void ColoredPetriNetBuilder::computePartition(){
        auto partitionStart = std::chrono::high_resolution_clock::now();
        Colored::PartitionBuilder pBuilder = Colored::PartitionBuilder(&_transitions, &_places, &_placePostTransitionMap, &_placePreTransitionMap);
        pBuilder.partitionNet();
        //pBuilder.printPartion();
        _partition = pBuilder.getPartition();
        pBuilder.assignColorMap(_partition);
        _partitionComputed = true;
        auto partitionEnd = std::chrono::high_resolution_clock::now();
        _partitionTimer = (std::chrono::duration_cast<std::chrono::microseconds>(partitionEnd - partitionStart).count())*0.000001;
    }
      
    void ColoredPetriNetBuilder::computePlaceColorFixpoint(uint32_t maxIntervals, uint32_t maxIntervalsReduced, int32_t timeout) {
        //Start timers for timing color fixpoint creation and max interval reduction steps
        auto start = std::chrono::high_resolution_clock::now();
        std::chrono::_V2::system_clock::time_point end = std::chrono::high_resolution_clock::now();
        auto reduceTimer = std::chrono::high_resolution_clock::now();        
        while(!_placeFixpointQueue.empty()){
            //Reduce max interval once timeout passes
            if(maxIntervals > maxIntervalsReduced && timeout > 0 && std::chrono::duration_cast<std::chrono::seconds>(end - reduceTimer).count() >= timeout){
                maxIntervals = maxIntervalsReduced; 
            }
            
            uint32_t currentPlaceId = _placeFixpointQueue.back();
            _placeFixpointQueue.pop_back();
            _placeColorFixpoints[currentPlaceId].inQueue = false;
            std::vector<uint32_t> connectedTransitions = _placePostTransitionMap[currentPlaceId];

            for (uint32_t transitionId : connectedTransitions) {                
                Colored::Transition& transition = _transitions[transitionId];
                // Skip transitions that cannot add anything new,
                // such as transitions with only constants on their arcs that have been processed once 
                if (transition.considered) continue;
                bool transitionActivated = true;
                transition.variableMaps.clear();

                if(!_arcIntervals.count(transitionId)){
                    _arcIntervals[transitionId] = setupTransitionVars(transition);
                }           
                processInputArcs(transition, currentPlaceId, transitionId, transitionActivated, maxIntervals);
         
                //If there were colors which activated the transitions, compute the intervals produced
                if (transitionActivated) {
                    processOutputArcs(transition);
                }          
            }
            end = std::chrono::high_resolution_clock::now();
        }

        _fixpointDone = true;
        _fixPointCreationTime = (std::chrono::duration_cast<std::chrono::microseconds>(end - start).count())*0.000001;

        //printPlaceTable();
        _placeColorFixpoints.clear();
    }

    //Create Arc interval structures for the transition
    std::unordered_map<uint32_t, Colored::ArcIntervals> ColoredPetriNetBuilder::setupTransitionVars(Colored::Transition transition){
        std::unordered_map<uint32_t, Colored::ArcIntervals> res;
        for(auto arc : transition.input_arcs){
            std::set<const Colored::Variable *> variables;
            std::unordered_map<uint32_t, const Colored::Variable *> varPositions;
            std::unordered_map<const Colored::Variable *, std::vector<std::unordered_map<uint32_t, int32_t>>> varModifiersMap;
            arc.expr->getVariables(variables, varPositions, varModifiersMap);

            Colored::ArcIntervals newArcInterval(&_placeColorFixpoints[arc.place], varModifiersMap);
            res[arc.place] = newArcInterval;               
        }
        return res;
    }

    void ColoredPetriNetBuilder::createPartionVarmaps(){
        for(uint32_t transitionId = 0; transitionId < _transitions.size(); transitionId++){
            Colored::Transition &transition = _transitions[transitionId];
            std::set<const Colored::Variable *> variables;
            _arcIntervals[transitionId] = setupTransitionVars(transition);

            for(auto inArc : transition.input_arcs){
                Colored::ArcIntervals& arcInterval = _arcIntervals[transitionId][inArc.place];
                uint32_t index = 0;
                arcInterval._intervalTupleVec.clear();
                PetriEngine::Colored::ColorFixpoint cfp;
                
                Colored::intervalTuple_t intervalTuple;
                intervalTuple.addInterval(_places[inArc.place].type->getFullInterval());
                cfp.constraints = intervalTuple;                              

                inArc.expr->getArcIntervals(arcInterval, cfp, &index, 0);
                _partition[inArc.place].applyPartition(arcInterval);
            }

            intervalGenerator.getVarIntervals(transition.variableMaps, _arcIntervals[transitionId]);
            for(auto outArc : transition.output_arcs){
                outArc.expr->getVariables(variables);
            }
            if(transition.guard != nullptr){
                transition.guard->getVariables(variables);
            }
            for(auto var : variables){
                for(auto &varmap : transition.variableMaps){
                    if(varmap.count(var) == 0){
                        Colored::intervalTuple_t intervalTuple;
                        intervalTuple.addInterval(var->colorType->getFullInterval());
                        varmap[var] = intervalTuple;
                    }
                }
            }
        }
    }

    //Retrieve color intervals for the input arcs based on their places
    void ColoredPetriNetBuilder::getArcIntervals(Colored::Transition& transition, bool &transitionActivated, uint32_t max_intervals, uint32_t transitionId){
        for (auto arc : transition.input_arcs) {
            PetriEngine::Colored::ColorFixpoint& curCFP = _placeColorFixpoints[arc.place];
            curCFP.constraints.restrict(max_intervals);
            _maxIntervals = std::max(_maxIntervals, (uint32_t) curCFP.constraints.size());
           
            Colored::ArcIntervals& arcInterval = _arcIntervals[transitionId][arc.place];
            uint32_t index = 0;
            arcInterval._intervalTupleVec.clear();

            if(!arc.expr->getArcIntervals(arcInterval, curCFP, &index, 0)){
                transitionActivated = false;
                return;
            }
            
            if(_partitionComputed){
                _partition[arc.place].applyPartition(arcInterval);  
            }                  
        }
    }

    void removeInvalidVarmaps(Colored::Transition& transition){
        std::vector<std::unordered_map<const Colored::Variable *, Colored::intervalTuple_t>> newVarmaps;
        for(auto& varMap : transition.variableMaps){
            bool validVarMap = true;      
            for(auto& varPair : varMap){
                if(!varPair.second.hasValidIntervals()){
                    validVarMap = false;
                    break;
                } else {
                    varPair.second.simplify();
                }
            } 
            if(validVarMap){
                newVarmaps.push_back(std::move(varMap));
            }                   
        }
        transition.variableMaps = std::move(newVarmaps);
    }

    //Retreive interval colors from the input arcs restricted by the transition guard
    void ColoredPetriNetBuilder::processInputArcs(Colored::Transition& transition, uint32_t currentPlaceId, uint32_t transitionId, bool &transitionActivated, uint32_t max_intervals) {     
        getArcIntervals(transition, transitionActivated, max_intervals, transitionId);  
        
        if(!transitionActivated){
            return;
        }
        if(intervalGenerator.getVarIntervals(transition.variableMaps, _arcIntervals[transitionId])){              
            if(transition.guard != nullptr) {
                transition.guard->restrictVars(transition.variableMaps);              
                removeInvalidVarmaps(transition);

                if(transition.variableMaps.empty()){
                    //Guard restrictions removed all valid intervals
                    transitionActivated = false;
                    return;
                }
            }
        } else {
            //Retrieving variable intervals failed
            transitionActivated = false;
        }                                            
    }

    void ColoredPetriNetBuilder::processOutputArcs(Colored::Transition& transition) {
        bool transitionHasVarOutArcs = false;

        for (auto& arc : transition.output_arcs) {
            Colored::ColorFixpoint& placeFixpoint = _placeColorFixpoints[arc.place];
            //used to check if colors are added to the place. The total distance between upper and
            //lower bounds should grow when more colors are added and as we cannot remove colors this
            //can be checked by summing the differences
            uint32_t colorsBefore = placeFixpoint.constraints.getContainedColors();
                
            std::set<const Colored::Variable *> variables;
            arc.expr->getVariables(variables);           

            if (!variables.empty()) {
                transitionHasVarOutArcs = true;
            }

            //Apply partitioning to unbound outgoing variables such that 
            // bindings are only created for colors used in the rest of the net
            if(!_partition[arc.place].diagonal){
                for(auto outVar : variables){
                    for(auto& varMap : transition.variableMaps){
                        if(varMap.count(outVar) == 0){
                            Colored::intervalTuple_t varIntervalTuple;
                            for(auto EqClass : _partition[arc.place]._equivalenceClasses){
                                varIntervalTuple.addInterval(EqClass._colorIntervals.back().getSingleColorInterval());
                            }
                            varMap[outVar] = varIntervalTuple;
                        }                    
                    }                
                }
            }

            auto intervals = arc.expr->getOutputIntervals(transition.variableMaps);
            intervals.simplify();

            for(auto& interval : intervals._intervals){
                placeFixpoint.constraints.addInterval(std::move(interval));    
            }
            placeFixpoint.constraints.simplify();

            //Check if the place should be added to the queue
            if (!placeFixpoint.inQueue) {
                uint32_t colorsAfter = placeFixpoint.constraints.getContainedColors();
                if (colorsAfter > colorsBefore) {
                    _placeFixpointQueue.push_back(arc.place);
                    placeFixpoint.inQueue = true;
                }
            }                   
        }
        //If there are no variables among the out arcs of a transition 
        // and it has been activated, there is no reason to cosider it again
        if(!transitionHasVarOutArcs) {
            transition.considered = true;
        }
    }

    //----------------------- Unfolding -----------------------//

    PetriNetBuilder& ColoredPetriNetBuilder::unfold() {
        if (_stripped) assert(false);
        if (_isColored && !_unfolded) {
            std::cout << "Unfolding " << _fixpointDone << _partitionComputed << std::endl;
            auto start = std::chrono::high_resolution_clock::now();

            if(!_fixpointDone && _partitionComputed){
                createPartionVarmaps();
            }
            
            for (auto& transition : _transitions) {
                unfoldTransition(transition);
            }
            auto unfoldedPlaceMap = _ptBuilder.getPlaceNames();
            for (auto& place : _places) {
               handleOrphanPlace(place, unfoldedPlaceMap);
            }
            
            _unfolded = true;
            auto end = std::chrono::high_resolution_clock::now();
            _time = (std::chrono::duration_cast<std::chrono::microseconds>(end - start).count())*0.000001;
        }
        return _ptBuilder;
    }

    //Due to the way we unfold places, we only unfold palces connected to an arc (which makes sense)
    //However, in queries asking about orphan places it cannot find these, as they have not been unfolded
    //so we make a placeholder place which just has tokens equal to the number of colored tokens
    //Ideally, orphan places should just be translated to a constant in the query
    void ColoredPetriNetBuilder::handleOrphanPlace(Colored::Place& place, std::unordered_map<std::string, uint32_t> unfoldedPlaceMap) {
        if(_ptplacenames.count(place.name) <= 0){
            std::string name = place.name + "_orphan";
            _ptBuilder.addPlace(name, place.marking.size(), 0.0, 0.0);
            _ptplacenames[place.name][0] = std::move(name);
        } else {
            uint32_t usedTokens = 0;
            
            for(std::pair<const uint32_t, std::string> unfoldedPlace : _ptplacenames[place.name]){
                auto unfoldedMarking = _ptBuilder.initMarking();
                auto unfoldedPlaceId = unfoldedPlaceMap[unfoldedPlace.second];
                usedTokens += unfoldedMarking[unfoldedPlaceId];
            }
            
            if(place.marking.size() > usedTokens){
                std::string name = place.name + "_orphan";
                _ptBuilder.addPlace(name, place.marking.size() - usedTokens, 0.0, 0.0);
                _ptplacenames[place.name][UINT32_MAX] = std::move(name);
            }
        }
        
        //++_nptplaces;        
    }
    
    void ColoredPetriNetBuilder::unfoldPlace(const Colored::Place* place, const PetriEngine::Colored::Color *color, uint32_t placeId, uint32_t id) {        
        size_t tokenSize = 0;
        if(!_partitionComputed || _partition[placeId].diagonal){
            tokenSize = place->marking[color];
        }else {
            for(auto colorEqClassPair : _partition[placeId].colorEQClassMap){
                if(colorEqClassPair.second->_id == _partition[placeId].colorEQClassMap[color]->_id){
                    tokenSize += place->marking[colorEqClassPair.first];
                }                    
            }
        }
            
        std::string name = place->name + "_" + std::to_string(color->getId());
        _ptBuilder.addPlace(name, tokenSize, 0.0, 0.0);
        _ptplacenames[place->name][id] = std::move(name);
        ++_nptplaces;
    }

    void ColoredPetriNetBuilder::unfoldTransition(Colored::Transition& transition) {
        if(_fixpointDone || _partitionComputed){            
            FixpointBindingGenerator gen(transition, _colors);
            size_t i = 0;
            
            for (auto b : gen) {                 
                std::string name = transition.name + "_" + std::to_string(i++);
                _ptBuilder.addTransition(name, 0.0, 0.0);
                _pttransitionnames[transition.name].push_back(name);
                ++_npttransitions;
                
                for (auto& arc : transition.input_arcs) {
                    unfoldArc(arc, b, name );
                }
                for (auto& arc : transition.output_arcs) {
                    unfoldArc(arc, b, name);
                }                
            }            
        } else {
            std::cout << "Entered naive" << std::endl;
            NaiveBindingGenerator gen(transition, _colors);
            size_t i = 0;
            for (auto b : gen) {              
                std::string name = transition.name + "_" + std::to_string(i++);
                _ptBuilder.addTransition(name, 0.0, 0.0);
                _pttransitionnames[transition.name].push_back(name);
                ++_npttransitions;
                for (auto& arc : transition.input_arcs) {
                    unfoldArc(arc, b, name);
                }
                for (auto& arc : transition.output_arcs) {
                    unfoldArc(arc, b, name);
                }
            }
        }        
    }

    void ColoredPetriNetBuilder::unfoldArc(Colored::Arc& arc, Colored::ExpressionContext::BindingMap& binding, std::string& tName) {
        Colored::ExpressionContext context {binding, _colors, _partition[arc.place]};
        auto ms = arc.expr->eval(context);       
        
        for (const auto& color : ms) {
            if (color.second == 0) {
                continue;
            }
            
            const PetriEngine::Colored::Place& place = _places[arc.place];
            uint32_t id;
            if(!_partitionComputed || _partition[arc.place].diagonal){
                id = color.first->getId();
            } else {
                id = _partition[arc.place].colorEQClassMap[color.first]->_id;
            }
            const std::string& pName = _ptplacenames[place.name][id];
            if (pName.empty()) {                               
                unfoldPlace(&place, color.first, arc.place, id);               
            }
            
            if (arc.input) {
                _ptBuilder.addInputArc(pName, tName, false, color.second);
            } else {
                _ptBuilder.addOutputArc(tName, pName, color.second);
            }
            ++_nptarcs;
        }        
    }

    //----------------------- Strip Colors -----------------------//

    PetriNetBuilder& ColoredPetriNetBuilder::stripColors() {
        if (_unfolded) assert(false);
        if (_isColored && !_stripped) {
            for (auto& place : _places) {
                _ptBuilder.addPlace(place.name, place.marking.size(), 0.0, 0.0);
            }

            for (auto& transition : _transitions) {
                _ptBuilder.addTransition(transition.name, 0.0, 0.0);
                for (auto& arc : transition.input_arcs) {
                    try {
                        _ptBuilder.addInputArc(_places[arc.place].name, _transitions[arc.transition].name, false,
                                                arc.expr->weight());
                    } catch (Colored::WeightException& e) {
                        std::cerr << "Exception on input arc: " << arcToString(arc) << std::endl;
                        std::cerr << "In expression: " << arc.expr->toString() << std::endl;
                        std::cerr << e.what() << std::endl;
                        exit(ErrorCode);
                    }
                }
                for (auto& arc : transition.output_arcs) {
                    try {
                        _ptBuilder.addOutputArc(_transitions[arc.transition].name, _places[arc.place].name,
                                                arc.expr->weight());
                    } catch (Colored::WeightException& e) {
                        std::cerr << "Exception on output arc: " << arcToString(arc) << std::endl;
                        std::cerr << "In expression: " << arc.expr->toString() << std::endl;
                        std::cerr << e.what() << std::endl;
                        exit(ErrorCode);
                    }
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
}
    
 