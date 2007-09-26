package com.learningrx.ComprehensionFigures
{
	import com.learningrx.*;
	import com.learningrx.ComprehensionFigures.*;

	public class Turns
	{
		private static var _RulesAndDefs:Class = com.learningrx.ComprehensionFigures.RulesAndDefinitions;
		
		public static function GetLevelsAndSublevels():Object
		{
			var sublevels:Object = new Object();
			sublevels.NumberOfLevels = NumberOfLevels;
			for (var i:Number = 1; i <= NumberOfLevels; ++i)
			{
				sublevels[i] = GetNumberOfSublevels(i);
			}
			return sublevels;
		}

		public static function GetNumberOfSublevels(pLevel:Number):Number
		{
			return Utilities.ObjectLength(Levels[pLevel].Sublevels);
		}

		public static function get NumberOfLevels():Number
		{
			return Utilities.ObjectLength(Levels);
		}

		public static function get TurnsPerRound():Object
		{
			return _RulesAndDefs.TURNS_PER_ROUND;
		}

		public static function get RightAnswerPauseSeconds():Object
		{
			return _RulesAndDefs.RIGHT_ANSWER_PAUSE_SECONDS;
		}

		public static function get WrongAnswerPauseSeconds():Object
		{
			return _RulesAndDefs.WRONG_ANSWER_PAUSE_SECONDS;
		}

		public static function get Speeds():Object
		{
			return _RulesAndDefs.SPEEDS;
		}

		public static function get TurnNumToHideKey():Object
		{
			return _RulesAndDefs.TURN_NUM_TO_HIDE_KEY;
		}

		public static function get SublevelToHideKey():Object
		{
			return _RulesAndDefs.SUBLEVEL_TO_HIDE_KEY;
		}

		public static function get SublevelToHideFindText():Object
		{
			return _RulesAndDefs.SUBLEVEL_TO_HIDE_FIND_TEXT;
		}

		public static function get TurnTimerInterval():Object
		{
			return _RulesAndDefs.TURN_TIMER_INTERVAL;
		}

		public static function get NumberOfAnswerBoxes():Object
		{
			return _RulesAndDefs.NUMBER_OF_ANSWER_BOXES;
		}

		public static function get Levels():Object
		{
			return _RulesAndDefs.LEVELS;
		}

		public static function get Shapes():Array
		{
			return _RulesAndDefs.SHAPES;
		}

		public static function get Objects():Array
		{
			return _RulesAndDefs.OBJECTS;
		}

		public static function get Positions():Object
		{
			return _RulesAndDefs.POSITIONS;
		}
		
		public static function GetFindText(pTurn:Object,
													  pLevelRules:Object):String
		{
			var positionDescription:String;
			var findText:String;
			findText = Utilities.Capitalize(pTurn.Descriptions[0], false) + ' ' + 
			                                pTurn.Positions[0].Text[Utilities.RandRange(0, pTurn.Positions[0].Text.length - 1)]
													  + ' ' + pTurn.Descriptions[1];
			if (pLevelRules.NumberOfFigures > 2)
			{
				positionDescription = pTurn.Positions[1].Text[Utilities.RandRange(0, pTurn.Positions[1].Text.length - 1)];
				if (positionDescription == "inside")
				{
					positionDescription = ', both ' + positionDescription;
				}
				else
				{
					positionDescription = ' ' + positionDescription;
				}
				findText += positionDescription + ' ' + pTurn.Descriptions[2];
				if (pLevelRules.NumberOfFigures > 3)
				{
					positionDescription = pTurn.Positions[2].Text[Utilities.RandRange(0, pTurn.Positions[2].Text.length - 1)];
					if (positionDescription == "inside")
					{
						positionDescription = ', all ' + positionDescription;
					}
					else
					{
						positionDescription = ' ' + positionDescription;
					}
					findText += positionDescription + ' ' + pTurn.Descriptions[3];
				}
			}
			findText += '.';
			return findText;
		}

		public static function GetRound(pLevel:Number,
												  pSublevel:Number,
												  pSpeed:Number):Object
		{
			var roundDetails:Object =  
			{
				NumberOfFigures: Levels[pLevel].NumberOfFigures,
				FigureType: Levels[pLevel].FigureType,
				Positions: Levels[pLevel].Positions,
				DescriptionTypes: Levels[pLevel].DescriptionTypes,
				Represent: Levels[pLevel].Represent,
				TurnToHideKey: Levels[pLevel].Sublevels[pSublevel].TurnToHideKey, 
				SecondsToHideFindText: Levels[pLevel].Sublevels[pSublevel].SecondsToHideFindText,
				SecondsPerTurn: Speeds[pSpeed]
			}
			return roundDetails;
		}

		public static function CreateKey(pNumberOfObjects:Number):Array
		{
			var key:Array = new Array();
			var chosenObjects:Array = new Array();
			var chosenShapes:Array = new Array();
			for (var i:Number = 0; i < pNumberOfObjects; ++i)
			{
				var item:Object = new Object();
				item.Shape = GetUniqueRandomShape(chosenShapes);
				chosenShapes.push(item.Shape);
				var cfObject:Object = GetUniqueRandomObject(chosenObjects);
				item.Name = cfObject.Name;
				chosenObjects.push(cfObject);
				key.push(item);
			}
			return key;			
		}
		
		public static function CreateTurn(pGame:Game, 
													 pLevelRules:Object, 
													 pCode:Array):Object
		{
			var turn:Object = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
			turn.distractors = CreateDistractors(pGame, pLevelRules, pCode, turn);
			return turn;
		}
		
		public static function IsFigureAShape(pName:String):Boolean
		{
			var firstTry:Object = GetShapeByName(pName);
			if (firstTry != null)
			{
				return true;
			}
			return false;
		}

//------------------------------------------------------------------------------

		private static function CreateDistractors(pGame:Game, 
															   pLevelRules:Object, 
																pCode:Array,
																pTurn:Object):Array
		{
			var distractors:Array = new Array();
			if (pLevelRules.NumberOfFigures == 2 && pLevelRules.Represent == "object")
			{
				return Create2x2Distractors(pLevelRules, pCode, pTurn);
			}
			else
			{
				switch (pLevelRules.NumberOfFigures)
				{
					case 2:
						{
							return Create2x1Distractors(pLevelRules, pCode, pTurn);
						}
					case 3:
						{
							return Create3x2Distractors(pLevelRules, pCode, pTurn);
						}
					case 4:
						{
							return Create4x3Distractors(pLevelRules, pCode, pTurn);
						}
					
				}
			}
		}
				
		private static function Create2x2Distractors(pLevelRules:Object, 
																   pCode:Array,
																   pTurn:Object):Array
		{
			var distractors:Array = new Array();
			{
				distractors.push({Figures: [pTurn.Figures[1], pTurn.Figures[0]], Positions: [pTurn.Positions[0]]});
				var positionsArray:Array = new Array(Positions[pLevelRules.Positions[0]][0], Positions[pLevelRules.Positions[0]][1]);
				if (Utilities.ArrayContains(positionsArray, pTurn.Positions[0]))
				{
					positionsArray = new Array(Positions[pLevelRules.Positions[1]][0], Positions[pLevelRules.Positions[1]][1]);
				}
				distractors.push({Figures: [pTurn.Figures[0], pTurn.Figures[1]], Positions: [positionsArray[0]]});
				distractors.push({Figures: [pTurn.Figures[1], pTurn.Figures[0]], Positions: [positionsArray[0]]});
			}
			return ShuffleDistractors(distractors);
		}
		
		private static function Create2x1Distractors(pLevelRules:Object, 
																   pCode:Array,
																   pTurn:Object):Array
		{
			var distractors:Array = new Array();
			var distractor:Object = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
			distractor.Figures[0] = pTurn.Figures[1];
			distractor.Figures[1] = pTurn.Figures[0];
			distractor.Positions = pTurn.Positions;
			distractors.push(distractor);
			for (var i:Number = 0; i < 2; ++i)
			{
				do 
				{
					distractor = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
				}
				while (HasAlreadyBeenChosen(pTurn, distractors, distractor))
				distractors.push(distractor);
			}
			return ShuffleDistractors(distractors);
		}
		
		private static function Create3x2Distractors(pLevelRules:Object, 
																   pCode:Array,
																   pTurn:Object):Array
		{
			var distractors:Array = new Array();
			var distractor:Object = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
			for (var k:Number = 0; k < pLevelRules.NumberOfFigures; ++k)
			{
				distractor.Figures[k] = pTurn.Figures[k];
			}
			for (k = 0; k < pLevelRules.NumberOfFigures; ++k)
			{
				distractor.Positions[k] = pTurn.Positions[k];
			}
			distractor.Figures[0] = pTurn.Figures[1];
			distractor.Figures[1] = pTurn.Figures[0];
			distractor.Positions = pTurn.Positions;
			distractors.push(distractor);
			distractor = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
			for (k = 0; k < pLevelRules.NumberOfFigures; ++k)
			{
				distractor.Figures[k] = pTurn.Figures[k];
			}
			distractor.Positions[0] = pTurn.Positions[1];
			distractor.Positions[1] = pTurn.Positions[0];
			distractors.push(distractor);
			do 
			{
				distractor = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
				distractor.Figures[0] = pTurn.Figures[0];
				distractor.Figures[1] = pTurn.Figures[1];
				distractor.Positions[0] = pTurn.Positions[0];
			}
			while (HasAlreadyBeenChosen(pTurn, distractors, distractor))
			distractors.push(distractor);
			return ShuffleDistractors(distractors);
		}

		private static function Create4x3Distractors(pLevelRules:Object, 
																   pCode:Array,
																   pTurn:Object):Array
		{
			var distractors:Array = new Array();
			var distractor:Object = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
			for (var k:Number = 0; k < pLevelRules.NumberOfFigures; ++k)
			{
				distractor.Figures[k] = pTurn.Figures[k];
			}
			for (k = 0; k < pLevelRules.NumberOfFigures; ++k)
			{
				distractor.Positions[k] = pTurn.Positions[k];
			}
			distractor.Figures[0] = pTurn.Figures[1];
			distractor.Figures[1] = pTurn.Figures[0];
			distractor.Positions = pTurn.Positions;
			distractors.push(distractor);
			distractor = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
			for (k = 0; k < pLevelRules.NumberOfFigures; ++k)
			{
				distractor.Figures[k] = pTurn.Figures[k];
			}
			distractor.Positions[0] = pTurn.Positions[1];
			distractor.Positions[1] = pTurn.Positions[0];
			distractors.push(distractor);
			do 
			{
				distractor = GetFiguresPositionsAndDescriptions(pLevelRules, pCode);
				distractor.Figures[0] = pTurn.Figures[0];
				distractor.Figures[1] = pTurn.Figures[1];
				distractor.Positions[0] = pTurn.Positions[0];
			}
			while (HasAlreadyBeenChosen(pTurn, distractors, distractor))
			distractors.push(distractor);
			return ShuffleDistractors(distractors);
		}

		private static function ShuffleDistractors(pTempDistractors:Array):Array
		{
			var distractors:Array = new Array();
			switch (Utilities.RandRange(1, 6))
			{
				case 1:
					distractors.push(pTempDistractors[0]);
					distractors.push(pTempDistractors[1]);
					distractors.push(pTempDistractors[2]);
					break;
				case 2:
					distractors.push(pTempDistractors[0]);
					distractors.push(pTempDistractors[2]);
					distractors.push(pTempDistractors[1]);
					break;
				case 3:
					distractors.push(pTempDistractors[1]);
					distractors.push(pTempDistractors[2]);
					distractors.push(pTempDistractors[0]);
					break;
				case 4:
					distractors.push(pTempDistractors[1]);
					distractors.push(pTempDistractors[0]);
					distractors.push(pTempDistractors[2]);
					break;
				case 5:
					distractors.push(pTempDistractors[2]);
					distractors.push(pTempDistractors[0]);
					distractors.push(pTempDistractors[1]);
					break;
				case 6:
					distractors.push(pTempDistractors[2]);
					distractors.push(pTempDistractors[1]);
					distractors.push(pTempDistractors[0]);
					break;
			}
			return distractors;
		}

		private static function GetRandomShape():Object
		{
			var shape:Object = Utilities.GetRandomValueFromArray(Shapes);
			return shape;
		}

		private static function GetUniqueRandomShape(pShapesToExclude:Array):Object
		{
			//trace('GetUniqueRandomShape', pShapesToExclude);
			return Utilities.GetUniqueRandomValueFromArray(Shapes, pShapesToExclude);
		}

		private static function GetRandomObject():Object
		{
			return Utilities.GetRandomValueFromArray(Objects);
		}

		private static function GetUniqueRandomObject(pObjectsToExclude:Array):Object
		{
			return Utilities.GetUniqueRandomValueFromArray(Objects, pObjectsToExclude);
		}

		private static function GetShapeByName(pName:String):Object
		{
			for (var i:Number = 0; i < Shapes.length; ++i)
			{
				if (pName == Shapes[i].Name)
				{
					return Shapes[i];
				}
			}
			return null;
		}

		private static function GetObjectByName(pName:String):Object
		{
			for (var i:Number = 0; i < Objects.length; ++i)
			{
				if (pName == Objects[i].Name)
				{
					return Objects[i];
				}
			}
			return null;
		}

		private static function GetFigureByName(pName:String):Object
		{
			var firstTry:Object = GetShapeByName(pName);
			if (firstTry != null)
			{
				return firstTry;
			}
			return GetObjectByName(pName);
		}

		private static function GetRandomFigure(pFigureType:String):Object
		{
			var figure:Object;
			switch (pFigureType.toUpperCase())
			{
				case 'SHAPE':
					figure = GetRandomShape();
					break;
				case 'OBJECT':
					figure = GetRandomObject();
					break;
			}
			return figure;
		}
		
		private static function GetRandomPosition(pPositionLevels:Array):Object
		{
			var positionLevel:Number = Utilities.GetRandomValueFromArray(pPositionLevels);
			var position = Utilities.GetRandomValueFromArray(Positions[positionLevel]);
			return position;
		}

		private static function GetUniqueRandomPosition(pPositionLevels:Array, 
																		pPositionsToExclude:Array):Object
		{
			var totalNumOfPositions:Number = 0;
			for (var i:Number = 0; i < pPositionLevels.length; ++i)
			{
				totalNumOfPositions += Positions[pPositionLevels[i]].length;
			}
			if (pPositionsToExclude.length >= totalNumOfPositions)
			{
				return null;
			}
			var position:Object;
			do
			{
				position = GetRandomPosition(pPositionLevels);
			}
			while (Utilities.ArrayContains(pPositionsToExclude, position));
			return position;
		}

		private static function GetDescription(pFigure:Object, 
															pDescriptionTypes:Array):String
		{
			var description:String;
			switch (Utilities.GetRandomValueFromArray(pDescriptionTypes).toUpperCase())
			{
				case 'NAME':
					if ('shorts' == pFigure.Name)
					{
						description = 'a pair of shorts';
					}
					else if ('elephant' == pFigure.Name)
					{
						description = 'an elephant';
					}
					else if ('octagon' == pFigure.Name)
					{
						description = 'an octagon';
					}
					else
					{
						description = 'a ' + pFigure.Name;
					}
					break;
				case 'DESCRIPTION':
					description = Utilities.GetRandomValueFromArray(pFigure.Descriptions);
					break;
				case 'FUNCTION':
					description = Utilities.GetRandomValueFromArray(pFigure.Functions);
					break;
			}
			return description;
		}
		
		private static function GetFiguresPositionsAndDescriptions(pLevelRules:Object, 
																					  pCode:Array)
		{
			var value:Object = new Object();
			value.Figures = new Array();
			value.Positions = new Array();
			value.Descriptions = new Array();
			var chosenItems:Array = new Array();
			var item:Object
			for (var i:Number = 0; i < pLevelRules.NumberOfFigures; ++i)
			{
				if ('self' == pLevelRules.Represent)
				{
					do 
					{
						item = GetRandomFigure(pLevelRules.FigureType);
					}
					while (Utilities.ArrayContains(chosenItems, item))
					chosenItems.push(item);
					value.Figures.push(item);
					value.Descriptions.push(GetDescription(value.Figures[i], pLevelRules.DescriptionTypes));
				}
				else
				{
					var codeItem:Object = Utilities.GetUniqueRandomValueFromArray(pCode, chosenItems);
					value.Figures.push(codeItem.Shape);
					chosenItems.push(codeItem);
					value.Descriptions.push(GetDescription(GetObjectByName(codeItem.Name), pLevelRules.DescriptionTypes));
				}
				if (i > 0) // we need 1 less rule than the number of figures
				{
					do
					{
						var position:Object = GetUniqueRandomPosition(pLevelRules.Positions, value.Positions);
					}
					while (IsBadCombination(i, position, pLevelRules.NumberOfFigures));
					value.Positions.push(position);
				}
			}
			return value;
		}
		
		private static function AreComplementaryPositions(pPosition1:String,
																		  pPosition2:String):Boolean
		{
			if ((pPosition1 == "Above" && pPosition2 == "Below") || (pPosition2 == "Above" && pPosition1 == "Below"))
			{
				return true;
			}
			if ((pPosition1 == "Inside" && pPosition2 == "Around") || (pPosition2 == "Inside" && pPosition1 == "Around"))
			{
				return true;
			}
			if ((pPosition1 == "Left" && pPosition2 == "Right") || (pPosition2 == "Left" && pPosition1 == "Right"))
			{
				return true;
			}
			if ((pPosition1 == "Higher" && pPosition2 == "Lower") || (pPosition2 == "Higher" && pPosition1 == "Lower"))
			{
				return true;
			}
			if ((pPosition1 == "Overlapping" && pPosition2 == "Overlapping"))
			{
				return true;
			}
			if ((pPosition1 == "Touching" && pPosition2 == "Touching"))
			{
				return true;
			}
			if ((pPosition1 == "Intersecting" && pPosition2 == "Intersecting"))
			{
				return true;
			}
			if ((pPosition1 == "Behind" && pPosition2 == "InFrontOf") || (pPosition2 == "Behind" && pPosition1 == "InFrontOf"))
			{
				return true;
			}
			return false;
		}
		
		private static function IsBadCombination(pFigureNumber:Number,
															  pPosition:Object,
															  pNumOfFigures:Number):Boolean
		{
			var bad:Boolean = false;
			if (pPosition.FunctionName == 'Inside' &&  pFigureNumber < pNumOfFigures - 2)
			{
				bad = true;
			}
			if (pPosition.FunctionName == 'Around' &&  pFigureNumber > 1)
			{
				bad = true;
			}
			//trace('IsBadCombination', pFigureNumber, pPosition.FunctionName, pNumOfFigures, bad);
			return bad;
		}

		private static function HasAlreadyBeenChosen(pTurn:Object,
																	pExistingDistractors:Array,
																   pProposedDistractor:Object):Boolean
		{
			if (HasSameFiguresAndPositions(pTurn, pProposedDistractor))
			{
				return true; 
			}
			if (pExistingDistractors.length > 0)
			{
				for (var i:Number = 0; i < pExistingDistractors.length; ++i)
				{
					if (HasSameFiguresAndPositions(pExistingDistractors[i], pProposedDistractor))
					{
						return true; 
					}
				}
			}
			return false;			
		}
			
		private static function HasSameFiguresAndPositions(pObject1:Object,
																		   pObject2:Object):Boolean
		{
			for (var i:Number = 0; i < pObject1.Figures.length - 1; ++i)
			{
				if (!IsDuplicatePositionAndFigures(pObject1.Figures[i].Name, pObject1.Figures[i + 1].Name, 
															  pObject2.Figures[i].Name, pObject2.Figures[i + 1].Name, 
															  pObject1.Positions[i].FunctionName, 
															  pObject2.Positions[i].FunctionName))
				{
					return false;
				}
			}
			return true;
		}
		
		private static function IsDuplicatePositionAndFigures(pObject1Figure1Name:String,
																		      pObject1Figure2Name:String,
																		      pObject2Figure1Name:String,
																		      pObject2Figure2Name:String,
																				pObject1Position:String,
																				pObject2Position:String):Boolean
		{
			var duplicate:Boolean = false
			if ((pObject1Position == pObject2Position))
			{			
				if ((pObject1Figure1Name == pObject2Figure1Name) && 
					 (pObject1Figure2Name == pObject2Figure2Name))
				{
					duplicate = true;
				}
			}
			if (AreComplementaryPositions(pObject1Position, pObject2Position))
			{			
				if ((pObject1Figure1Name == pObject2Figure2Name) && 
					 (pObject1Figure2Name == pObject2Figure1Name))
				{
					duplicate =  true;
				}
			}
			return duplicate;
		}
	}
}