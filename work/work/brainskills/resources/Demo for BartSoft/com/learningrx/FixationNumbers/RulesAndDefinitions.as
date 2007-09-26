package com.learningrx.FixationNumbers
{
	public class RulesAndDefinitions
	{
		public static const DISPLAY_TIMER_INTERVAL:Number = 100;
		public static const INTERVAL_TIMER_INTERVAL:Number = 100;
		public static const TURNS_PER_ROUND:Number = 50;
		public static const SPEEDS:Array = [{Display: 500, Interval: 2000},
														{Display: 400, Interval: 1500}, 
														{Display: 200, Interval: 1000}, 
														{Display: 150, Interval:  750}]; // In milliseconds
		public static const GAME_WIDTH:Number = 680;
		public static const GAME_HEIGHT:Number = 680;
		public static const NUMBER_COLORS:Array = ["blue", "green", "yellow", "red"];
		public static const NUMBER_COLOR_VALUES:Object = {blue: 0x3399FF, green: 0x00FF00, yellow: 0xFFFF00, red: 0xCC0000};
		
		public static const LEVELS:Object = {
		1: {AnswerType: "CircledNumbers",
			 NumberOfResponses: 10,
			 Hint: "Using the keypad, enter only the circled numbers.",
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		2: {AnswerType: "RedNumber",
			 NumberOfResponses: 12,
			 Hint: "Using the keypad, enter only the red numbers.",
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		3: {AnswerType: "OneAfterRedNumber",
			 Hint: "Enter each number that comes right after a red number.",
			 NumberOfResponses: 13,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		4: {AnswerType: "OneAfterTargetNumber",
			 Hint: "Enter each number that comes right after TARGET.",
			 NumberOfResponses: 14,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		5: {AnswerType: "OneBeforeRedNumber",
			 Hint: "Enter each number that comes before a red number.",
			 NumberOfResponses: 15,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		6: {AnswerType: "OneBeforeTargetNumber",
			 Hint: "Enter each number that comes before TARGET.",
			 NumberOfResponses: 16,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		7: {AnswerType: "OneAfterRedNumberPlus1",
			 Hint: "Enter each number after a red number, adding 1.",
			 NumberOfResponses: 17,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		8: {AnswerType: "OneAfterTargetNumberPlus2",
			 Hint: "Enter each number that comes after a TARGET, adding 2.",
			 NumberOfResponses: 18,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		9: {AnswerType: "OneBeforeRedNumberPlus3",
			 Hint: "Enter each number that comes before a red number, adding 3.",
			 NumberOfResponses: 19,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		10:{AnswerType: "OneBeforeTargetNumberDifference4",
			 Hint: "Enter the difference of each number that comes before TARGET and 4.",
			 NumberOfResponses: 20,
			 Sublevels: {1: ["Top", "Top"],
							 2: ["Top", "Bottom"],
							 3: ["Random", "Random"]}},
		11:{AnswerType: "OneBeforeRedNumberDifference3",
			 NumberOfResponses: 20,
			 Hint: "Enter the difference of each number before a red number and 3.",
			 Sublevels: {1: {ColumnA: "Top", ColumnB: "Top"},
							 2: {ColumnA: "Top", ColumnB: "Bottom"},
							 3: {ColumnA: "Random", ColumnB: "Random"}}},
		12:{AnswerType: "OneBeforeTargetNumberDifference9",
			 NumberOfResponses: 20,
			 Hint: "Enter the difference of each number that comes before TARGET and 9.",
			 Sublevels: {1: {ColumnA: "Top", ColumnB: "Top"},
							 2: {ColumnA: "Top", ColumnB: "Bottom"},
							 3: {ColumnA: "Random", ColumnB: "Random"}}}};
/*enter the difference of the number prior to the target number and the number after the given number
		13:{AnswerType: "RedNumber",
			 NumberOfResponses: 12,
			 Sublevels: {1: {ColumnA: "Top", ColumnB: "Top"},
							 2: {ColumnA: "Top", ColumnB: "Bottom"},
							 3: {ColumnA: "Random", ColumnB: "Random"}}}};
*/	
	}
}