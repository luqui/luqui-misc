package com.learningrx.VisualPuzzle
{
	import flash.display.*;
	import flash.events.*;
	import flash.utils.Timer;
	import flash.geom.*;
	import flash.ui.Keyboard;

	import com.learningrx.*
	import com.learningrx.Shared.*

	public class VisualPuzzle extends Exercise
	{
		private const MATCHING_DISTANCE = 14;
		
		private var _ResultsText:ResultsText;
		private var _StartRoundButton:StartRoundButton;
		private var _ImageLoader:ImageLoader;
		private var _ImageBitmap:Bitmap;
		private var _PictureBox:PictureBox;
		private var _ActiveChild:JigsawPiece;
		private var _LastActiveChild:JigsawPiece;
		private var _Children:Array = [[]];
		private var _NumberOfChildren = 0;
		private var _SolvingState:String = "none";
		private var _ImageWidth:Number = 600;
		private var _ImageHeight:Number = 450;
		private var _Offset:Point;
		private var _ImageFileFolder:String = 'images/';

		public function VisualPuzzle(pParent:Framework)
		{
			super(pParent, 'VisualPuzzle', com.learningrx.VisualPuzzle.Turns);
			InitListeners();
			InitRoundTimer();
			InitAnimateTimer();
		}

		override public function EndRound():void
		{
			super.EndRound();
			StopTimer(_AnimateTimer);
			StopTimer(_RoundTimer);
		}
		 
		override public function StartRound(pLevel:Number, 
														pSublevel:Number, 
														pSpeed:Number):void
		{
			super.StartRound(pLevel, pSublevel, pSpeed);
			InitListeners();
			ResetTimer(_RoundTimer);
			_Children = new Array();
			_NumberOfChildren = _RoundDetails.Rows * _RoundDetails.Columns;
			_ImageLoader = new ImageLoader(this, _ImageFileFolder + _RoundDetails.ImageFileName, OnImageLoadComplete);
			_Parent.ShowScoreAndDivider('false');
		}

		override public function ResetEverything():void
		{
			StopTimer(_AnimateTimer);
			StopTimer(_RoundTimer);
			ClearStage();
		}
		
		override public function OnStartRoundButtonClicked():void
		{
			_SecondsElapsedInRound = 0;
			RestartTimer(_AnimateTimer);
			RestartTimer(_RoundTimer);
			for (var row:Number = 0; row < _RoundDetails.Rows ; ++row)
			{
				for (var col:Number = 0; col < _RoundDetails.Columns; ++col)
				{
					_Children[row][col].Start();
				}
			}
			if ('separate' == _RoundDetails.Behavior)
			{
				InitSeparateTimer();
				RestartTimer(_SeparateTimer);
			}
			//ShowSolution();
		}

		private function InitPictureBox(pImage:Bitmap):void
		{
			_PictureBox = new PictureBox(this, _ImageWidth / 5, _ImageHeight / 5);
			_PictureBox.Show(pImage);
			_PictureBox.x = Framework.EXERCISE_WIDTH - _PictureBox.width - 12;
			_PictureBox.y = 12;
			Utilities.Show(this, _PictureBox);
		}
		
		private function InitListeners():void
		{
			_Stage.addEventListener(KeyboardEvent.KEY_DOWN, OnKeyDown);
			_Stage.addEventListener(MouseEvent.MOUSE_MOVE, OnMouseMove);
			_Stage.addEventListener(MouseEvent.MOUSE_UP, OnMouseUp);
		}

		private function RemoveListeners():void
		{
			_Stage.removeEventListener(KeyboardEvent.KEY_DOWN, OnKeyDown);
			_Stage.removeEventListener(MouseEvent.MOUSE_MOVE, OnMouseMove);
			_Stage.removeEventListener(MouseEvent.MOUSE_UP, OnMouseUp);
		}

		private function OnMouseMove(pEvent:MouseEvent):void
		{
			if (_SolvingState == "none" && null != _ActiveChild)
			{
				_ActiveChild.MoveTo(pEvent.stageX - _Offset.x, pEvent.stageY - _Offset.y);	
				pEvent.updateAfterEvent();
			}
		}
	
		public function ChildPressed(pChild:JigsawPiece):void
		{
			ActivateChild(pChild);
			_Offset = new Point(_Stage.mouseX - pChild.x, 
									  _Stage.mouseY - pChild.y);
		}

		private function OnMouseUp(pEvent:MouseEvent):void
		{
			if (_SolvingState == "none" && null != _ActiveChild)
			{
				MatchPieces(_ActiveChild);
				UnactivateChild();
				if (PuzzleSolved())
				{
					_RightAnswers = 1;
					_WrongAnswers = 0;
					EndRound();
				}
			}
		}

		private function OnKeyDown(pEvent:KeyboardEvent):void
		{
			if (pEvent.keyCode == Keyboard.RIGHT || 
				 pEvent.keyCode == Keyboard.DOWN || 
				 pEvent.keyCode == Keyboard.SPACE)
			{
				RotateLastActiveChild(90);
			}
			else if (pEvent.keyCode == Keyboard.LEFT || 
						pEvent.keyCode == Keyboard.UP)
			{
				RotateLastActiveChild(270);
			}
		}

		private function OnImageLoadComplete()
		{
			_ImageBitmap = _ImageLoader.Content;
			_ImageWidth = _ImageBitmap.width;
			_ImageHeight = _ImageBitmap.height;
			InitPictureBox(_ImageBitmap);
			CreatePuzzle();
		}

		private function CreatePuzzle()
		{
			for (var row:Number = 0; row < _RoundDetails.Rows ; ++row)
			{
				_Children.push([]);
				for (var col:Number = 0; col < _RoundDetails.Columns; ++col)
				{
					_Children[row].push(CreatePiece(row, col));
					Utilities.Show(this, _Children[row][col]);
				}
			}
		}

		private function CreatePiece(pRow:Number,
											  pCol:Number,
											  pTopEdge:Number = NaN,
											  pRightEdge:Number = NaN,
											  pBottomEdge:Number = NaN,
											  pLeftEdge:Number = NaN):JigsawPiece
		{
			var pieceWidth:Number = _ImageWidth / _RoundDetails.Columns;
			var pieceHeight:Number = _ImageHeight / _RoundDetails.Rows;
			var pieceX:Number = pCol * pieceWidth;
			var pieceY:Number = pRow * pieceHeight;
			var rightEdge:Number = (Utilities.RandRange(0, 1) > 0 ? (1) : (-1)) *
											(Utilities.RandRange(1, _RoundDetails.Edges.length - 2));
			if (!isNaN(pRightEdge))
			{
				rightEdge = pRightEdge;
			}
			var bottomEdge:Number = (Utilities.RandRange(0, 1) > 0 ? (1) : (-1)) * 
											 (Utilities.RandRange(1, _RoundDetails.Edges.length - 2));
			if (!isNaN(pBottomEdge))
			{
				bottomEdge = pBottomEdge;
			}
			var topEdge:Number;
			if (!isNaN(pTopEdge))
			{
				topEdge = pTopEdge;
			}
			else
			{
				topEdge = pRow == 0 ? (0) : (-_Children[pRow - 1][pCol].Pieces[0].bottomEdge);
			}
			var leftEdge:Number;
			if (!isNaN(pLeftEdge))
			{
				leftEdge = pLeftEdge;
			}
			else
			{
				leftEdge =  pCol == 0 ? (0) : (-_Children[pRow][pCol - 1].Pieces[0].rightEdge);
			}
			var piece:Object = 
			{
				x: pieceX, 
				y: pieceY, 
				width: pieceWidth, 
				height: pieceHeight, 
				col: pCol,
				row: pRow, 
				topEdge: topEdge, 
				rightEdge: pCol == _RoundDetails.Columns - 1 ? (0) : (rightEdge), 
				bottomEdge: pRow == _RoundDetails.Rows - 1 ? (0) : (bottomEdge), 
				leftEdge: leftEdge,
				rotation: Utilities.RandRange(0, (_RoundDetails.MaximumRotation / 90)) * 90
			};
			var jigsawPiece:JigsawPiece = new JigsawPiece(this, _ImageBitmap, _RoundDetails.Edges, new Array(piece));
			if ('amble' == _RoundDetails.Behavior)
			{
				jigsawPiece.Ambling = true;
			}
			jigsawPiece.x = (BackgroundWidth - _ImageWidth) / 2;
			jigsawPiece.y = (BackgroundWidth - _ImageHeight) / 2 - 140;
			return jigsawPiece;
		}

		private function AreNeighbors(pChild1:JigsawPiece,
												pChild2:JigsawPiece):Boolean
		{
			return (pChild1 != null && pChild2 != null && pChild1 != pChild2);
		}

		private function PuzzleSolved():Boolean
		{
			if (_NumberOfChildren == _Children[0][0].PiecesCount && _Children[0][0].rotation == 0)
			{
				_Children[0][0].RemoveMask();
				_Children[0][0].RemoveMouseListener();
				return true;
			}
			return false;
		}

		private function MatchPieces(pChild:JigsawPiece):void
		{
			var match:JigsawPiece = null;
			for (var i:Number = 0; i < pChild.PiecesCount; ++i)
			{
				var col:Number = pChild.Pieces[i].col;
				var row:Number = pChild.Pieces[i].row;
				if (col > 0 && ChildrenTouching(pChild, _Children[row][col - 1]))
				{
					match = _Children[row][col - 1];
				}
				else if (row > 0 && ChildrenTouching(pChild, _Children[row - 1][col]))
				{
					match = _Children[row - 1][col];
				}
				else if (row < _RoundDetails.Rows - 1 && ChildrenTouching(pChild, _Children[row + 1][col]))
				{
					match = _Children[row + 1][col];
				}
				else if (col < _RoundDetails.Columns - 1 && ChildrenTouching(pChild, _Children[row][col + 1]))
				{
					match = _Children[row][col + 1];
				}
			}
			if (match != null)
			{
				if ('separate' == _RoundDetails.Behavior)
				{
					RestartTimer(_SeparateTimer);
				}
				match.Absorb(pChild);
				match.Ambling = false;
				for (i = 0; i < pChild.PiecesCount; ++i)
				{
					_Children[pChild.Pieces[i].row][pChild.Pieces[i].col] = match;
				}
				Utilities.RemoveChildFromDisplayList(this, pChild);
				if (match.Pieces.length > 3)
				{
					Utilities.MoveChildToBottomOfDisplayList(this, match);
				}
				MatchPieces(match); // Just in case we might be next to more than one.
			}
		}

		private function ChildrenTouching(pChild1:JigsawPiece,
													 pChild2:JigsawPiece):Boolean
		{
			if (pChild1 == null || pChild2 == null || pChild1 == pChild2)
			{
				return false;
			}
			else if (pChild1.rotation != pChild2.rotation)
			{
				return false;
			}
			else if (Utilities.Distance({x: pChild1.x, y: pChild1.y}, 
												 {x: pChild2.x, y: pChild2.y}) > MATCHING_DISTANCE)
			{
				return false;
			}
			else
			{
				return true;
			}
		}

		private function ClearStage()
		{
			if (_RoundDetails != null)
			{
				for (var row:Number = 0; row < _RoundDetails.Rows; ++row)
				{
					for (var col:Number = 0; col < _RoundDetails.Columns; ++col)
					{
						Utilities.RemoveChildFromDisplayList(this, _Children[row][col]);
						_Children[row][col] = null;
					}
				}
			}
		}

		private function ActivateChild(pChild:JigsawPiece):void
		{
			if (pChild != null)
			{
				UnactivateChild();
				_ActiveChild = pChild;
				_LastActiveChild = pChild;
				Utilities.MoveChildToTopOfDisplayList(this, pChild);
				_ActiveChild.Lift();
			}
		}

		private function UnactivateChild()
		{
			if (_ActiveChild != null)
			{
				_ActiveChild.Drop();
				_ActiveChild = null;
			}
		}

		private function RotateActiveChild(pAngle:Number):void
		{
			_ActiveChild.Rotate(pAngle);
			if (PuzzleSolved())
			{
				_RightAnswers = 1;
				_WrongAnswers = 0;
				EndRound();
			}
		}

		private function RotateLastActiveChild(pAngle:Number):void
		{
			if (_LastActiveChild != null)
			{
				_LastActiveChild.Rotate(pAngle);
				if (PuzzleSolved())
				{
					_RightAnswers = 1;
					_WrongAnswers = 0;
					EndRound();
				}
			}
		}
		
		private function SeparateAChild(pEvent:TimerEvent):void
		{
			outerLoop: for (var row:Number = 0; row < _RoundDetails.Rows ; ++row)
			{
				for (var col:Number = 0; col < _RoundDetails.Columns; ++col)
				{
					if (_Children[row][col].PiecesCount > 1)
					{
						var piece:Object = _Children[row][col].Pieces.pop();
						Utilities.RemoveLastChildFromDisplayList(_Children[row][col].MaskSprite);
						_Children[piece.row][piece.col] = CreatePiece(piece.row, piece.col, 
																					 piece.topEdge, piece.rightEdge, 
																					 piece.bottomEdge, piece.leftEdge);
						Utilities.AddChildToDisplayList(this, _Children[piece.row][piece.col]);
						_Children[piece.row][piece.col].Start();
						break outerLoop;
					}
				}
			}
			RestartTimer(_SeparateTimer);
		}
		
		private function AnimateChildren(pEvent:TimerEvent):void
		{
			if (_SolvingState != 'none')
			{
				SolvingPilot();
			}
			var animatedChildren:Array = new Array();
			for (var row:Number = 0; row < _RoundDetails.Rows ; ++row)
			{
				for (var col:Number = 0; col < _RoundDetails.Columns; ++col)
				{
					if (!Utilities.ArrayContains(animatedChildren, _Children[row][col]))
					{
						animatedChildren.push(_Children[row][col])
						_Children[row][col].Animate();
					}
				}
			}
		}

		public function get ImageWidth():Number
		{
			return _ImageWidth;
		}
		
		public function get ImageHeight():Number
		{
			return _ImageHeight;
		}
		
		public function get Rows():Number
		{
			return _RoundDetails.Rows;
		}
		
		public function get Columns():Number
		{
			return _RoundDetails.Columns;
		}
		
		// ----------------------------

		public function ShowSolution():void
		{
			RestartTimer(_AnimateTimer);
			_SolvingState = 'init';
			SolvingPilot();
		}

		private function SolvingPilot():void
		{
			switch (_SolvingState)
			{
				case 'stop':
					_SolvingState = "none";
					_ActiveChild.StopMoving();
					StopTimer(_AnimateTimer);
					break;
				case "init":
					ActivateChild(_Children[0][0]);
					_SolvingState = "rotate";
					break;
				case "rotate":
					if (_ActiveChild.rotation % 360 != 0)
					{
						RotateActiveChild(-15);
					}
					else
					{
						_SolvingState = "move";
					}
					break;
				case "move":
					_ActiveChild.BeginMoving((BackgroundWidth - _ImageWidth) / 2, 
													 (BackgroundWidth - _ImageHeight) / 2 - 100);
					_SolvingState = "wait";
					break;
				case "wait":
					if (!_ActiveChild.Moving)
					{
						_SolvingState = "match";
					}
					break;
				case "match":
					_ActiveChild.Drop();
					if (_ActiveChild != _Children[0][0])
					{
						MatchPieces(_ActiveChild);
					}
					else
					{
						Utilities.MoveChildToBottomOfDisplayList(this, _Children[0][0]);
					}
					_SolvingState = "next";
					break;
				case "next":
					if (PuzzleSolved())
					{
						_SolvingState = "none";
						StopTimer(_AnimateTimer);
					}
					else
					{
						for (var row:Number = 0; row < _RoundDetails.Rows; ++row)
						{
							for (var col:Number = 0; col < _RoundDetails.Columns; ++col)
							{
								if (_Children[row][col] != _Children[0][0])
								{
									ActivateChild(_Children[row][col]);
									_SolvingState = "rotate";
									break;
								}
							}
							if (_SolvingState == "rotate")
							{
								break;
							}
						}
					}
					break;
			}
		}

		private function InitAnimateTimer():void
		{
			_AnimateTimer = new Timer(Turns.AnimateTimerInterval);
			_AnimateTimer.addEventListener(TimerEvent.TIMER, AnimateChildren);
		}

		private function InitSeparateTimer():void
		{
			_SeparateTimer = new Timer(500, _RoundDetails.TimePerPiece / 500);
			_SeparateTimer.addEventListener(TimerEvent.TIMER_COMPLETE, SeparateAChild);
		}

		private function InitRoundTimer():void
		{
			_RoundTimer = new Timer(Framework.ROUND_TIMER_INTERVAL);
			_RoundTimer.addEventListener(TimerEvent.TIMER, OnRoundTimer);
		}

		private function OnRoundTimer(pEvent:TimerEvent):void 
		{
			++_SecondsElapsedInRound;
			var millisecondsElapsed = _SecondsElapsedInRound * 1000;
			_Parent.UpdateProgressBar(Math.min(100, (millisecondsElapsed / _RoundDetails.Time) * 100));
			trace(_RoundDetails.Time, millisecondsElapsed, millisecondsElapsed / _RoundDetails.Time);
			if (millisecondsElapsed >= _RoundDetails.Time)
			{
				_RightAnswers = 0;
				_WrongAnswers = 1;
				EndRound();
			}
		}
	}
}