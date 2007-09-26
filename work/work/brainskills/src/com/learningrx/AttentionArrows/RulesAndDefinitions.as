package com.learningrx.AttentionArrows
{
	import flash.ui.Keyboard;
	
	public class RulesAndDefinitions
	{
		public static const AUDIO_DISTRACTIONS_RATE = 1;
		public static const DISTRACTION_ARROW_SPIN_SPEED:Number = 30;

		public static const SPEEDS:Array = [{ArrowsPerRound: 20, MilliSecondsPerBeat: 1500}, 
														{ArrowsPerRound: 30, MilliSecondsPerBeat: 1000},
														{ArrowsPerRound: 40, MilliSecondsPerBeat: 670},
														{ArrowsPerRound: 50, MilliSecondsPerBeat: 500}];
		public static const CLICK_WINDOWS:Object = {1500: 1500 / 8, 1000: 1000 / 8, 670: 670 / 8, 500: 500 / 8};
		public static const METRONOME_TIMER_INTERVAL:Number = 10;
		public static const CONSECUTIVE_ERRORS_FOR_VOLUME_INCREASE:Number = 2;
		public static const CONSECUTIVE_RIGHT_ANSWERS_FOR_VOLUME_DECREASE:Number = 3;
		public static const MAXIMUM_VOLUME:Number = 100;
		public static const MINIMUM_VOLUME:Number = 70;
		public static const VOLUME_CHANGE_FACTOR:Number = 10;
		public static const MOVING_ARROW_EASE_PERCENT:Number = .5;
		public static const ARROW_COLORS:Array = ["blue", "green", "yellow", "red"];
		public static const ARROW_COLOR_VALUES:Object = {blue: 0x3399FF, green: 0x00FF00, yellow: 0xFFFF00, red: 0xCC0000};
		public static const DIRECTIONS:Array = ["up", "right", "down", "left"];
		public static const OPPOSITE_DIRECTIONS:Object = {up: "down", right: "left", down: "up", left: "right"};
		public static const CLOCKWISE_DIRECTIONS:Object = {up: "right", right: "down", down: "left", left: "up"};
		public static const ROTATIONS:Object = {up: 0, right: 90, down: 180, left: 270};
		
		public static const LEVELS:Object = 
		{
			1: {AnswerType: "Same",
				 Distractions: {MovingArrows: 2,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: false},
				 Metronome: false,
				 Sublevels: {1: {Factor: "Orientation", Motion: false, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: false, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			2: {AnswerType: "Same",
				 Distractions: {MovingArrows: 3,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: false},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: false, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: true, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			3: {AnswerType: "Opposite",
				 Distractions: {MovingArrows: 3,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: false},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: true, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			4: {AnswerType: "OppositeOnRedOrGreen",
				 Distractions: {MovingArrows: 4,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: false},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: true, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			5: {AnswerType: "Clockwise",
				 Distractions: {MovingArrows: 4,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: false},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: true, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			6: {AnswerType: "ClockwiseOnBlueOrYellow",
				 Distractions: {MovingArrows: 5,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: false},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: true, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			7: {AnswerType: "OppositeIfColorEqualsPrevious",
				 Distractions: {MovingArrows: 5,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: true},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Motion", Motion: true, ShowDistractions: false},
								 3: {Factor: "Orientation", Motion: true, ShowDistractions: true},
								 4: {Factor: "Motion", Motion: true, ShowDistractions: true}}},
			8: {AnswerType: "Pattern",
				 Distractions: {MovingArrows: 6,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: true},
				 Metronome: true,
				 Sublevels: {1: {Factor: "OrientationEveryThird", Motion: true, ShowDistractions: false},
								 2: {Factor: "OrientationEveryThird", Motion: true, ShowDistractions: true},
								 3: {Factor: "OrientationEveryOther", Motion: true, ShowDistractions: false},
								 4: {Factor: "OrientationEveryOther", Motion: true, ShowDistractions: true}}},
			9: {AnswerType: "SameIfOrientationEqualsMotion",
				 Distractions: {MovingArrows: 6,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: true},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Orientation", Motion: true, ShowDistractions: true}}},
			10:{AnswerType: "SwitchOnRed",
				 Distractions: {MovingArrows: 6,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: true},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Orientation", Motion: true, ShowDistractions: true}}},
			11:{AnswerType: "SameIfOrientationEqualsMotionClockwiseOnRed",
				 Distractions: {MovingArrows: 6,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: true},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Orientation", Motion: true, ShowDistractions: true}}},
			12:{AnswerType: "SameIfOrientationEqualsMotionClockwiseIfColorEqualsPrevious",
				 Distractions: {MovingArrows: 6,
									 SpinningArrows: 1,
									 Alpha: 0.5,
									 AudioDistractions: true},
				 Metronome: true,
				 Sublevels: {1: {Factor: "Orientation", Motion: true, ShowDistractions: false},
								 2: {Factor: "Orientation", Motion: true, ShowDistractions: true}}}
		}
	}
}