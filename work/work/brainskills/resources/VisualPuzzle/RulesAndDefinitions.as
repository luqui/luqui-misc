package com.learningrx.VisualPuzzle
{
   public class RulesAndDefinitions
   {
		public static const ANIMATE_TIMER_INTERVAL:Number = 20;
		public static const SPEEDS:Object = 
		{
			1:
			{
				TimePerPiece: 6000
			},
			2:
			{
				TimePerPiece: 2400
			}, 
			3:
			{
				TimePerPiece: 1800
			}, 
			4:
			{
				TimePerPiece: 1500
			}
		}; // In milliseconds

		public static const TIME_PER_LEVEL_ADJUSTMENT:Number = 1500;
		public static const EXERCISE_WIDTH:Number = 680;
		public static const EXERCISE_HEIGHT:Number = 680;
		public static const PUZZLE_IMAGES:Array = 
		[
			'beach.jpg', 
			'pleiades.jpg',
			'turret.jpg',
			'bridge.jpg',
			'columbia.jpg',
			'pomegranate.jpg',
			'ghosttown.jpg',
			'broccoli.jpg',
			'clouds.jpg',
			'apricots.jpg',
			'cheese.jpg',
			'daisy.jpg',
			'nightview.jpg',
			'arch.jpg',
			'tiger.jpg',
			'hazelnuts.jpg',
			'pagoda.jpg',
			'peugeot.jpg',
			'frog.jpg',
			'nuts.jpg',
			'lion.jpg',
			'barn.jpg',
			'cart.jpg',
			'lake.jpg',
			'peacock.jpg'
		];
			
		public static const INSTRUCTIONS:Object = 
		{
			1: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			2: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			3: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			4: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			5: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			6: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			7: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			8: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			9: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			},
			10: 
			{	Sublevels: 
				{
					1: 'Use your mouse to click and drag the puzzle pieces. Put the puzzle together before time runs out.',
					2: 'Put the puzzle together before time runs out. If you are too slow, the pieces will begin to come ' +
						'back apart.',
					3: 'Catch the moving pieces with your mouse. Use them to put the puzzle together before time runs out.'
				}
			}
		};
		public static const LEVELS:Object = 
		{
			1: 
			{
				ShapeStyle: 'Square',
				ImageFileName: 'cart.jpg',
				MaximumRotation: 0,
				Flipping: 0,
				Backside: 'none',
				Columns: 3,
				Rows: 3,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			2: 
			{
				ShapeStyle: 'Square',
				ImageFileName: 'pagoda.jpg',
				MaximumRotation: 0,
				Flipping: 0,
				Backside: 'none',
				Columns: 3,
				Rows: 3,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			3: 
			{
				ShapeStyle: 'Triangle',
				ImageFileName: 'bridge.jpg',
				MaximumRotation: 90,
				Flipping: 0,
				Backside: 'none',
				Columns: 3,
				Rows: 4,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			4: 
			{
				ShapeStyle: 'Triangle',
				ImageFileName: 'peacock.jpg',
				MaximumRotation: 90,
				Flipping: 0,
				Backside: 'none',
				Columns: 4,
				Rows: 3,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			5: 
			{
				ShapeStyle: 'Oval',
				ImageFileName: 'peugeot.jpg',
				MaximumRotation: 270,
				Flipping: 0,
				Backside: 'none',
				Columns: 4,
				Rows: 3,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			6: 
			{
				ShapeStyle: 'Oval',
				ImageFileName: 'cheese.jpg',
				MaximumRotation: 270,
				Flipping: 0,
				Backside: 'none',
				Columns: 4,
				Rows: 3,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			7: 
			{
				ShapeStyle: 'Mixed',
				ImageFileName: 'clouds.jpg',
				MaximumRotation: 270,
				Flipping: 0,
				Backside: 'none',
				Columns: 4,
				Rows: 4,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			8: 
			{
				ShapeStyle: 'Mixed',
				ImageFileName: 'broccoli.jpg',
				MaximumRotation: 270,
				Flipping: 0,
				Backside: 'none',
				Columns: 4,
				Rows: 4,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			9: 
			{
				ShapeStyle: 'Classic',
				ImageFileName: 'peacock.jpg',
				MaximumRotation: 270,
				Flipping: 0,
				Backside: 'none',
				Columns: 4,
				Rows: 4,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			},
			10:
			{
				ShapeStyle: 'Classic',
				ImageFileName: 'hazelnuts.jpg',
				MaximumRotation: 270,
				Flipping: 0,
				Backside: 'none',
				Columns: 6,
				Rows: 4,
				Sublevels: 
				{
					1: 'normal',
					2: 'separate',
					3: 'amble'
				}
			}
		};
		public static const EDGES:Object = 
		{
			Mixed: [
				[[0, 0], [100, 0]],
				[[0, 0], [30, 0], [40, -16, 30, -16], [50, 0, 50, -16], [50, 16], [70, 16], [70, 0], [100, 0]], 
				[[0, 0], [30, 0], [40, -16, 30, -16], [50, 0, 50, -16], [65, 16], [80, 0], [100, 0]], 
				[[0, 0], [30, 0], [30, -16], [50, -16], [50, 0], [65, 16], [80, 0], [100, 0]], 
				[[0, 0], [30, 0], [30, -16], [50, -16], [50, 0], [60, 16, 50, 16], [70, 0, 70, 16], [100, 0]], 
				[[0, 0], [20, 0], [35, -16], [50, 0], [50, 16], [70, 16], [70, 0], [100, 0]], 
				[[0, 0], [20, 0], [35, -16], [50, 0], [60, 16, 50, 16], [70, 0, 70, 16], [100, 0]], 
				[[0, 0], [30, 0], [40, 16, 30, 16], [50, 0, 50, 16], [50, -16], [70, -16], [70, 0], [100, 0]], 
				[[0, 0], [30, 0], [40, 16, 30, 16], [50, 0, 50, 16], [50, 0], [50, 0], [65, -16], [80, 0], [100, 0]], 
				[[0, 0], [30, 0], [30, 16], [50, 16], [50, 0], [65, -16], [80, 0], [100, 0]], 
				[[0, 0], [30, 0], [30, 16], [50, 16], [50, 0], [60, -16, 50, -16], [70, 0, 70, -16], [100, 0]], 
				[[0, 0], [20, 0], [35, 16], [50, 0], [50, -16], [70, -16], [70, 0], [100, 0]], 
				[[0, 0], [20, 0], [35, 16], [50, 0], [60, -16, 50, -16], [70, 0, 70, -16], [100, 0]]],
			Square: [
				[[0, 0], [100, 0]],
				[[0, 0], [20, 0], [20, -16], [40, -16], [40, 0], [60, 0],   [60, 16],  [80, 16],  [80, 0],  [100, 0]], 
				[[0, 0], [30, 0], [30, -16], [50, -16], [50, 0], [50, 16],  [70, 16],  [70, 0],   [100, 0]], 
				[[0, 0], [30, 0], [30, -16], [50, -16], [50, 0], [60, 0],   [60, 16],  [80, 16],  [80, 0],  [100, 0]], 
				[[0, 0], [20, 0], [20, 16],  [40, 16],  [40, 0], [60, 0],   [60, -16], [80, -16], [80, 0],  [100, 0]], 
				[[0, 0], [30, 0], [30, 16],  [50, 16],  [50, 0], [50, -16], [70, -16], [70, 0],   [100, 0]], 
				[[0, 0], [30, 0], [30, 16],  [50, 16],  [50, 0], [60, 0],   [60, -16], [80, -16], [80, 0],  [100, 0]]],
			Triangle: [
				[[0, 0], [100, 0]],
				[[0, 0], [10, 0], [25, -16], [40, 0], [60, 0],   [75, 16],  [90, 0], [100, 0]], 
				[[0, 0], [15, 0], [30, -16], [45, 0], [55, 0],   [70, 16],  [85, 0], [100, 0]], 
				[[0, 0], [20, 0], [35, -16], [50, 0], [65, 16],  [80, 0],   [100, 0]], 
				[[0, 0], [10, 0], [25, 16],  [40, 0], [60, 0],   [75, -16], [90, 0], [100, 0]], 
				[[0, 0], [15, 0], [30, 16],  [45, 0], [55, 0],   [70, -16], [85, 0], [100, 0]], 
				[[0, 0], [20, 0], [35, 16],  [50, 0], [65, -16], [80, 0],   [100, 0]]],
			Oval: [
				[[0, 0], [100, 0]], 
				[[0, 0], [15, 0], [25, -16, 15, -16], [35, 0, 35, -16], [65, 0], [75, 16, 65, 16], [85, 0, 85, 16], [100, 0]], 
				[[0, 0], [25, 0], [35, -16, 25, -16], [45, 0, 45, -16], [55, 0], [65, 16, 55, 16], [75, 0, 75, 16], [100, 0]], 
				[[0, 0], [30, 0], [40, -16, 30, -16], [50, 0, 50, -16], [60, 16, 50, 16], [70, 0, 70, 16], [100, 0]], 
				[[0, 0], [15, 0], [25, 16, 15, 16],   [35, 0, 35, 16],  [65, 0], [75, -16, 65, -16], [85, 0, 85, -16], [100, 0]], 
				[[0, 0], [25, 0], [35, 16, 25, 16],   [45, 0, 45, 16],  [55, 0], [65, -16, 55, -16], [75, 0, 75, -16], [100, 0]], 
				[[0, 0], [30, 0], [40, 16, 30, 16],   [50, 0, 50, 16],  [60, -16, 50, -16], [70, 0, 70, -16], [100, 0]]],
		   Classic: [
				[[0, 0], [100, 0]], 
				[[0, 0], [32, 0, 42, 16], [40, -16, 12, -16], [48, 0, 60, -16], [100, 0, 40, 16], [100, 0]], 
				[[0, 0], [32, 0, 42, 16], [40, -16, 20, -16], [48, 0, 68, -16], [100, 0, 40, 16], [100, 0]], 
				[[0, 0], [42, 0, 52, 16], [50, -16, 30, -16], [58, 0, 78, -16], [100, 0, 48, 16], [100, 0]], 
				[[0, 0], [42, 0, 52, 16], [50, -16, 20, -16], [58, 0, 68, -16], [100, 0, 48, 16], [100, 0]], 
				[[0, 0], [52, 0, 60, 16], [60, -16, 30, -16], [68, 0, 80, -16], [100, 0, 60, 16], [100, 0]], 
				[[0, 0], [52, 0, 60, 16], [60, -16, 28, -16], [68, 0, 74, -16], [100, 0, 60, 16], [100, 0]]]
		};
	}
}